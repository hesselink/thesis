\section{Arbitrary number of type parameters}
%include polycode.fmt
%include forall.fmt
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%format ~ = "\sim"
%format undefined = "\bot"
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

What we want to do, is abstract over the number of type parameters a
type former takes. This means also abstracting over the kind of the
recursive positions. The idea is, to use numbers on the type level to
indicate the number of type parameters, and to indicate which type
parameter an element corresponds to.

In a dependently typed programming language, we can apply this idea
directly. [TODO: How do I insert Agda code in here?]

In Haskell, we can represent this as follows: we use a GADT containing
the types of all the elements. The constructors of this GADT hold a
value of one of these types, and we use a type level number to
indicate which one. This way, we can recover the type of the element
by pattern matching of the GADT. The functors now become:

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
the order of the parameters.
[TODO: clear up, example].

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
the functors, |a| and |b| have been instantiated to concrete types by
partially applying |Elems|, since it needs to have kind |* -> *|
there. Note that we need one of these GADTs for each arity (number of
type parameters).

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
datatype: no values of it can be constructed that are not |undefined| or
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

For this representation we also want to define a generic map function.
We start by defining a type class again for data types that have a
functor representation, and making |Tree| an instance. We define an
associated type for the elements. We use an associated type instead of
a multi parameter type class, because for the latter, the type of the
elements is too free, and the compiler cannot select the right
instance.

\begin{code}
class Ix a where
    type Es a :: * -> *
    from  :: a          -> PF a (Es a) a
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
do this inline because we are pattern matching on a GADT to recover
information about the index. The simplest way to define a function to
map over the elements, is to name it, and define it standalone. For
example, say we have a tree of |Int| and |String|, and we want to map
the |chr| and |length| function over them, turning it into a tree of
|Char| and |Int|. We can define the function to map over the tree as
follows:

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
|a' :||: es|. We do this by pattern matching on |Z| and |S|, thus
recovering the type index. If we have a |Z|, we know that it contains
an element of type |a'|, and we can apply the function |f| to it. If
we have an |S|, it contains something of type |es|, and we can apply
|fs| to that due to the context |Apply fs es|. The result type can be
calculated as the result type of the head of the list (which is just
function application) followed by the result type of the application
of the tail of the list.

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
