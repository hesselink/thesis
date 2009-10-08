\section{Arbitrary number of type parameters}
\label{sec:multiparam}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt
%options ghci -fglasgow-exts -pgmL lhs2tex -optL --pre
%if style == newcode
\begin{code}
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , GADTs
           , KindSignatures
           , EmptyDataDecls
           , MultiParamTypeClasses
           , FlexibleContexts
           , RankNTypes
           , FlexibleInstances
           #-}
import Data.Char(chr)
\end{code}
%endif

We want to abstract over the number of type parameters a type former
takes. This means also abstracting over the kind of the recursive
positions, since these have to take an arbitrary number of type
parameters. To do this, we will use numbers on the type level to
indicate the number of type parameters, and to indicate which type
parameter an element corresponds to.

In a dependently typed programming language, we can apply this idea
directly. In Haskell, we can represent this as follows: we use a GADT
containing the types of all the elements. The constructors of this
GADT hold a value of one of these types, and we use a type level
number to indicate which one. This way, we can recover the type of the
element by pattern matching of the GADT. The functors now become:

\begin{code}
data K a        (es :: * -> *) r = K a
data E a        (es :: * -> *) r = E (es a)
data I          (es :: * -> *) r = I r
data (f :*: g)  (es :: * -> *) r = f es r :*: g es r
data (f :+: g)  (es :: * -> *) r = L (f es r) | R (g es r)
\end{code}
%if style == newcode
\begin{code}
infixr 7 :*:
infixr 6 :+:
\end{code}
%endif

The type |a| in the type of |E| is the type level number, used to
indicate which type parameter it is. This ensures that we don't change
the order of the parameters. For example, if we have a type with two
type parameters, |T a b|, an |a| would be represented as |E Zero es
r|, and a |b| as |E (Suc Zero) es r|. By requiring these indices to
remain the same, we ensure that we don't accidentally use a |b| where
an |a| was expected.

Note that |r| has kind |*| again. Since we don't know how many type
parameters the type we are representing takes, and we have no kind
polymorphism available in Haskell, our only option is to refer to the
fully applied type including all type parameters. For example, in the
one element case, |r| could be |[]|, whereas now it would be |[a]|.

As an example of the GADT that holds the parameters, let us consider
representing a data type with two type parameters. The GADT will be as
follows:

\begin{code}
data Zero
data Suc a

data Elems :: * -> * -> * -> * where
    E0 :: a -> Elems a b Zero
    E1 :: b -> Elems a b (Suc Zero)
\end{code}

In essence, this is a container that can hold either |a|'s or |b|'s,
and uses |Zero| and |Suc Zero| to indicate which one. In the type of
the functors, |Elems| will have been partially applied to two types,
since it needs to have kind |* -> *| there. Note that we need one of
these GADTs for each arity (number of type parameters).

But we can do better. We can construct a GADT that can hold any number
of parameters, and indicates their position with a (type level)
numeric index. In essence, we build a \emph{list} of types, and index
into it using the type index. This type looks as follows:

\begin{code}
data (t :|: ts) :: * -> * where
  Z :: t     -> (t :|: ts) Zero
  S :: ts n  -> (t :|: ts) (Suc n)
\end{code}

%if style == newcode
\begin{code}
infixr 8 :|:
\end{code}
%endif

If the index is |Zero|, the type |t :||: ts| contains a |t|. If it is
|Suc n|, it contains a type |ts| (which can be another value of this
type) at an index of |n|. How do we end this list of types?  For that,
we need a data type other than |(:||:)| to instantiate |ts| with. It
needs to be of kind |* -> *|, and we will use the following
definition:

\begin{code}
data Nil a = Nil { magic :: forall a. a }
\end{code}

Although it may not look like it, this is supposed to be an empty
data type: no values of it can be constructed that are not |undefined| or
|Nil undefined|. Furthermore, if we somehow get a value of type |Nil
a| (for example, while defining a type class instance), we can write
the function using |magic|, instead of having to provide |undefined|
ourselves (compare with the absurd pattern in Agda
\cite{agdasummerschool}).

As a concrete example, consider a tree data type that stores one type
of value in its leaves, and another in the branches:

\begin{code}
data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b) deriving Show
\end{code}

We define a type family, and make an instance for |Tree|:

\begin{code}
type family PF a :: (* -> *) -> * -> *

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I
\end{code}

In the `from' function, we pack up the value in one of the
constructors of the |(:||:)|. In the `to' function, we pattern match on
this GADT, which allows us to return the correct type again.

\begin{code}
fromTree  :: Tree a b -> PF (Tree a b) (a :|: b :|: Nil) (Tree a b)
fromTree (Leaf a)        = L (E (Z a))
fromTree (Branch l b r)  = R (I l :*: E (S (Z b)) :*: I r)

toTree    :: PF (Tree a b) (a :|: b :|: Nil) (Tree a b) -> Tree a b
toTree (L (E (Z a)))                      = Leaf a
toTree (R (I l :*: E (S (Z b)) :*: I r))  = Branch l b r
\end{code}

\subsection{Generic map}

For the representation of a data type with an arbitrary number of type
parameters, we also want to define a generic map function.  We start
by defining a type class again for data types that have a functor
representation, and making |Tree| an instance. We define an associated
type for the elements. We use an associated type instead of a multi
parameter type class, because for the latter, the type of the elements
is too free, and the compiler cannot select the right instance.

\begin{code}
class Ix a where
    type Es a :: * -> *
    from  :: a              -> PF a (Es a) a
    to    :: PF a (Es a) a  -> a

instance Ix (Tree a b) where
    type Es (Tree a b) = (a :|: b :|: Nil)
    from  = fromTree
    to    = toTree
\end{code}

When mapping a function over a data type, we want to convert \emph{all}
element types to other types. To do this generically, the |gmap|
function will take a function that transforms a value from the element
system, for \emph{any} element index. We defined a type class |GMap|
again, and make all functors an instance of it.

The type class holds the function |gmap'| that takes two functions.
The first transforms the elements as described above. The second is
the function that should be applied at the recursive points, as we did
with the one parameter version. Again, this argument will not have to
be provided by the user, because we will define a top level function
|gmap| later that provides it.

\begin{code}
class GMap f where
    gmap' :: (forall n. es n -> es2 n) -> (r -> r') -> f es r -> f es2 r'
\end{code}

We again give instances of this class for all our functors. For a |K|,
we do nothing, and for an |I|, we apply the second argument to the
recursive structure contained within. In the |E| case, we do the
actual work, applying the function being mapped to an element. Since
this function can be applied to an element at any index, we can use it
without problems. For the sum and product, we just propagate the
function call to the next level as usual.

\begin{code}
instance GMap (K a) where
    gmap' _ _ (K a) = K a

instance GMap (E n) where
    gmap' f _ (E e) = E (f e)

instance GMap I where
    gmap' _ g (I r) = I (g r)

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap' f g (L x) = L (gmap' f g x)
    gmap' f g (R y) = R (gmap' f g y)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap' f g (x :*: y) = gmap' f g x :*: gmap' f g y
\end{code}

Now we can define a generic map function. The context says, first of
all, that the types that we map over, have to be instances of the
|Ix| class, i.e. they can be converted to a pattern functor. This
pattern functor should then be an instance of the |GMap| class, so we
can map over it. Finally, we require that the pattern functor of the
starting type and the result type are the same. This means we can only
change the elements, not the structure of the type. In the one
parameter case, this was a direct consequence of the type signature:
the type former |r| was the same in both types. Here, however, we
cannot see the type former anymore, since we have abstracted over its
kind. The actual definition of the function stays the same as before.

\begin{code}
gmap ::  (Ix a, Ix b, GMap (PF a), PF a ~ PF b) =>
         (forall n. Es a n -> Es b n) -> a -> b
gmap f = to . gmap' f (gmap f) . from
\end{code}

To use this generic map, we have to supply it with a function that
maps elements to new elements. This can be problematic, as we cannot
do this with an inline lambda expression, because we are pattern
matching on a GADT to recover information about the index. The
simplest way to define a function to map over the elements, is to name
it, and define it standalone. For example, say we have a tree of |Int|
and |String|, and we want to map the |chr| and |length| function over
them, turning it into a tree of |Char| and |Int|. We can define the
function to map over the tree as follows:

\begin{code}
f :: (Int :|: String :|: Nil) n -> (Char :|: Int :|: Nil) n
f (Z i)      = Z (chr i)
f (S (Z s))  = S (Z (length s))
f (S (S x))  = magic x
\end{code}

We can now apply it as follows:

\begin{code}
example :: Tree Int String
example = Branch (Leaf 101) "test" (Branch (Leaf 114) "element" (Leaf 105))

gmapExample :: Tree Char Int
gmapExample = gmap f example
\end{code}

However, this is not ideal. We would like to give the functions inline
when applying |gmap|. It turns out we can do this, using type classes
and associated type families. We define a type class for a form of
function application to indexed types:

\begin{code}
class Apply fs es where
  type Res fs es :: * -> *
  apply :: fs -> es n -> Res fs es n
\end{code}

The meaning of this class is as follows: by giving an instance of
|Apply fs es|, you show how |fs| can be applied to |es| while
preserving the index. The result type will be calculated from |fs| and
|es| by the type family |Res|.

We can give a case for |(:||:)|, applying a nested tuple of functions
to it:

\begin{code}
instance (a ~ a', Apply fs es) => Apply (a -> b, fs) (a' :|: es) where
  type Res (a -> b, fs) (a' :|: es) = b :|: Res fs es
  apply (f, fs) (Z x) = Z (f x)
  apply (f, fs) (S x) = S (apply fs x)
\end{code}

If we can apply |fs| to |es|, then we can also apply |(a -> b, fs)| to
|a' :||: es|, provided that |a ~ a'|. We do this by pattern matching
on |Z| and |S|, thus recovering the type index. If we have a |Z|, we
know that it contains an element of type |a'|, and we can apply the
function |f| to it. If we have an |S|, it contains something of type
|es|, and we can apply |fs| to that due to the context |Apply fs es|.
The result type can be calculated as the result type of the head of
the list (which is just function application) followed by the result
type of the application of the tail of the list.

Why don't we use the type |a| at the front of the list, and instead
have |a'| and an equality constraint |a ~ a'|? This is needed to allow
polymorphic functions to be applied to monomorphic values. If we apply
the function |length| which has type |[a] -> Int| to a value of type
|String| (which is a |[Char]|), the right instance won't be found
when we use only a type |a|, since |a| and |Char| are not the same
type. However, with the above instance |a| and |a'| don't have to be
the same, as long as they can be unified later to satisfy the equality
constraint.

We also need a case for |Nil|. We can give it directly, but it is more
convenient to instead define an instance for singleton lists, because
that way, we avoid having to pass an unused last element in the nested
tuple of functions.

\begin{code}
instance (a ~ a') => Apply (a -> b) (a' :|: Nil) where
  type Res (a -> b) (a' :|: Nil) = b :|: Nil
  apply f (Z x) = Z (f x)
  apply f (S x) = magic x
\end{code}

Now that we have these instances, we can give the function to map over
a structure inline. For convenience, we define an operator to
construct tuples infix, so we don't need parentheses.

\begin{code}
(&) = (,)
infixr 5 &

gmapExample2 :: Tree Char Int
gmapExample2 = gmap (apply $ chr & length) example
\end{code}

\subsection{Producers - generic zero}
\label{sec:multiparam:producers}

We can divide generic functions into three separate classes:
consumers, transformers and producers. Consumers are functions that
consume a type in a generic way, and output a concrete type.  Examples
are the show function or (structural) equality. Transformers consume a
type generically, but also produce a (possibly different) type
generically. The |gmap| function that was discussed is an example of a
transformer. The final class of functions are producers. These produce
values of a type generically, with only concrete types as input.
Examples are parsers, like the well-known |read| function, as well as
test data generation.

Writing one of each of these classes of functions is a good way to
test the quality of a generic programming framework: it should be
possible to express all of these functions in a framework. So far, we
have only written a transformer. We will now write a generic producer;
producers can often highlight shortcomings of the implementation,
since they do something interesting: they produce values `out of
nowhere'.

We will implement the `generic zero': a function that produces the
smallest value of a data type. For example, for lists, it would produce
the empty list, and for |Maybe|, it would produce |Nothing|. Some
data types have no obvious smallest value; for example, |Bool|. In
these cases, we make a choice to always either take the left or the
right constructor. This choice will be configurable with a boolean
parameter.

We again define the function using a type class, |HZero|. It provides
one function, |hzero|, which takes three arguments. The first is an
element, polymorphic in the index, i.e. it is a producer of elements.
The second is the value to put at the recursive position. We again do
not ask the user to provide this, but will `tie the knot' later. The
third is a boolean, which we will use in the case of a sum, as
mentioned earlier.

\begin{spec}
class HZero f where
  hzero :: (forall n. es n) -> r -> Bool -> f es r
\end{spec}

The case for |K| already gives us a problem: where do we get the value
to put inside? We define another type class for this: |Small|. This
type class contains values that have a `small' value: numbers, for
example, have |0|. We use this type class to generate the value inside
a |K| constructor.

\begin{code}
class Small a where
  small :: a
\end{code}

\begin{spec}
instance Small a => HZero (K a) where
  hzero _ _ _ = K small
\end{spec}

For elements, we use the first argument to |hzero|, and for recursive
positions, the second. In essence, this postpones the problem of
generating these values to a moment where we can solve it.

\begin{spec}
instance HZero (E n) where
  hzero e _ _ = E e

instance HZero I where
  hzero _ r _ = I r
\end{spec}

Sums give us a choice: we can go either left or right, and the choice
is completely arbitrary (though it is customary to have the smallest
constructor on the left), so we abstract from this choice. We use the
third, boolean argument to hzero to decide the sum constructor to use.
The instance for products is entirely straightforward.

\begin{spec}
instance (HZero f, HZero g) => HZero (f :+: g) where
  hzero e r True  = L $ hzero e r True
  hzero e r False = R $ hzero e r False

instance (HZero f, HZero g) => HZero (f :*: g) where
  hzero e r left = hzero e r left :*: hzero e r left
\end{spec}

We can now define our top level function, which we will call |gleft|.
This function will provide values for all the arguments to |hzero|.
For the boolean, will choose |True| to take a left constructor at
sums, since it is convention to have the smallest constructor on the
left. For recursive positions, we can just call |gleft| again.
However, we have no way to generate elements, so we will leave it up
to the caller to provide these.

\begin{spec}
gleft :: (Ix a, HZero (PF a)) => (forall n. Es a n) -> a
gleft f = to $ hzero f (gleft f) True
\end{spec}

However, a problem arises when we try to call this function to
generate, for example, a value of the |Tree| type defined earlier. It
turns out to be impossible to give the element generator. The reason
is that it is \emph{too polymorphic}: it says it can generate elements
for all |n|, but actually, |n| can only be of natural number types
(|Zero| and |Suc n|). In essence, the kind of |Es a| is not |* -> *|,
but |knat -> *|, where we use |knat| to indicate a kind that is
restricted the natural number types. We would like a Haskell syntax to
define kinds like this:

\begin{spec}
datakind Nat = Zero | Suc Nat
data Es a (ix :: Nat)
\end{spec}

Another option would be to define the type on the value level, and \emph{lift}
it to the type level. See for example `she' by Conor McBride \cite{web:she}.
The solution we use here, is to require a proof that |n| is a natural number
type to be passed. We define this proof as follows:

\begin{code}
data NatPrf :: knat -> * where
  PZ :: NatPrf Zero
  PS :: NatPrf n -> NatPrf (Suc n)
\end{code}

This data type states that |Zero| is a natural number type, and that
if |n| is a natural number type, then so is |Suc n|. By pattern
matching on this type, we can also recover the actual value. This is
another thing we need when generating values of |(:||:)|, because we
need to decide whether to generate a |Z| or an |S| constructor.

We will need to get a value of this proof at some point. Rather than
having the user produce it, we can generate it using a type class. The
type class |El| contains a proof that the index |ix| can be produced
in |prf|. We also give two instances for the natural number types.

\begin{code}
class El prf ix where
  proof :: prf ix

instance El NatPrf Zero where
  proof = PZ

instance El NatPrf n => El NatPrf (Suc n) where
  proof = PS proof
\end{code}

We can now give a new version of the |HZero| type class that is
additionally parametrized over a proof that is passed to the element
generating function. In the case for |E|, we require that the index be
in |prf|, and use the |proof| function to generate the actual proof.
The other cases are unchanged, and have no constraints on |prf|.

\begin{code}
class HZero prf f where
  hzero :: (forall n. prf n -> es n) -> r -> Bool -> f es r

instance Small a => HZero prf (K a) where
  hzero _ _ _ = K small

instance El prf n => HZero prf (E n) where
  hzero e _ _ = E (e proof)

instance HZero prf I where
  hzero _ r _ = I r

instance (HZero prf f, HZero prf g) => HZero prf (f :+: g) where
  hzero e r True  = L $ hzero e r True
  hzero e r False = R $ hzero e r False

instance (HZero prf f, HZero prf g) => HZero prf (f :*: g) where
  hzero e r left = hzero e r left :*: hzero e r left
\end{code}

We could now define a function to generate the elements by hand, but
it is more convenient to do this with a type class again. This type
class captures exactly the function we want to provide: it takes a
proof that the index is a natural number, and produces an element at
this position.

\begin{code}
class SmallEl es where
  smallEl :: NatPrf n -> es n

instance (Small a, SmallEl as) => SmallEl (a :|: as) where
  smallEl PZ     = Z small
  smallEl (PS p) = S (smallEl p)

instance SmallEl Nil where
  smallEl _ = Nil $ error "Nil generated in smallEl."
\end{code}

We can provide an instance for |(:||:)| by pattern matching on the
proof to recover the index: if we are at index zero, we produce an
actual value by calling |small|; if we are at a successor index, we
add an |S| constructor and use |smallEl| again for the tail, with the
proof we just unwrapped.

We also have to give an instance for |Nil|, since an instance for the
tail (|as|) is always required. However, we cannot give this instance,
so we resort to calling |error|. It is not possible for this to be
called in normal use of the generic functions; however, it can be
called manually, for example: |smallEl PZ :: Nil Zero|.

Using the type class |SmallEl| for generating elements, we can now
define an improved version of |gleft|. It calls |smallEl| to generate
elements and calls itself recursively to generate recursive values.

\begin{code}
gleft :: forall a. (Ix a, HZero NatPrf (PF a), SmallEl (Es a)) => a
gleft = to $ hzero smallEl gleft True
\end{code}

If we define suitable |Small| instances, we can now call, for example,
|gleft :: Tree Int Bool| to produce \eval{gleft :: Tree Int Bool}.

%if style == newcode
\begin{code}
instance Small Int where
  small = 0

instance Small Bool where
  small = False
\end{code}
%endif

We have introduced a method to generically represent elements of data
types with an arbitrary number of type parameters. We do this by
defining a container type to hold the elements. All functors are
parametrized by this container type. We index the container using type
level numbers to indicate the parameter position. This allows for type
safe conversion from and to the original data type.

Using this extension, we can define the generic mapping function
|gmap|. We have given a type class |Apply| which allows easily mapping
combinations of functions over our container type |(:||:)|. We have
also shown how to define a producer function using this
representation. This requires a \emph{proof} that the element index is
a natural number. We give a data type for such proofs, and a type
class to produce instances of such proofs.

The provided extension has none of the problems the previous two
representations (Sections \ref{sec:functorrep} and \ref{sec:oneparam}) had in
representing parametrized data types. In particular, we can now represent
regular data types with an arbitrary number of type parameters, and we have
access to these type parameters in our generic functions. The cost is added
complexity: we use a GADT to contain the elements of our data type, and in
generic producer functions, we additionally need proof terms.

The notion of using indexed functors to gain more expressivity has been
mentioned elsewhere \cite{indexedcontainers}. Similar ideas are also used in
multirec (Section \ref{sec:multirec}) and unpublished work by Conor McBride.
Techniques like this are also often used in dependently types languages like
Agda \cite{agdasummerschool}.
