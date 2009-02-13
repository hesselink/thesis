\section{Arbitrary number of type parameters}
%include polycode.fmt
%include forall.fmt
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%format ~ = "\sim"
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
           #-}
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

As a concrete example, consider a tree data type that stores one type
of value in its leaves, and another in the branches:

\begin{code}
data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b)
\end{code}

We define a type family, and make an instance for |Tree|:

\begin{code}
type family PF a :: (* -> *) -> * -> *

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I
\end{code}

In the `from' function, we pack up the value in one of the
constructors of the |Elems|. In the `to' function, we pattern match on
this GADT, which allows us to return the correct type again.

\begin{code}
fromTree  :: Tree a b -> PF (Tree a b) (Elems a b) (Tree a b)
fromTree (Leaf a)        = L (E (E0 a))
fromTree (Branch l b r)  = R (I l :*: E (E1 b) :*: I r)

toTree    :: PF (Tree a b) (Elems a b) (Tree a b) -> Tree a b
toTree (L (E (E0 a)))                  = Leaf a
toTree (R (I l :*: E (E1 b) :*: I r))  = Branch l b r
\end{code}

\subsection{Generic map}

For this representation we also want to define a generic map function.
We start by defining a type class again for data types that have a
functor representation, and making |Tree| an instance:

\begin{code}
class Ix es a where
    from  :: a          -> PF a es a
    to    :: PF a es a  -> a

instance Ix (Elems a b) (Tree a b) where
    from  = fromTree
    to    = toTree
\end{code}

When mapping a function over a data type, we want to conver \emph{all}
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
gmap ::  (Ix es a, Ix es2 b, GMap (PF a), PF a ~ PF b) =>
         (forall n. es n -> es2 n) -> a -> b
gmap f = to . gmap' f (gmap f) . from
\end{code}
