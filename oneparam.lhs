\section{Single type parameter}
\label{sec:oneparam}
\long\def\ignore#1{}
%include polycode.fmt
%include thesis.fmt
%options ghci -fglasgow-exts
%if style == newcode
\begin{code}
{-# OPTIONS_GHC -F -pgmF lhs2tex -optF --pre #-}
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , FlexibleContexts
           #-}
\end{code}
%endif

Using the functor representation to represent types with type
parameters, like |[a]|, is problematic. For example, suppose we want
to represent the list data type, which might be defined as:

\begin{spec}
data [a] = [] | a : [a]
\end{spec}

If we try to represent this in our view, we have to use |K| for the
elements. However, this implies that it is not possible to define
generic functions that operate on the elements of the list, since the
type of the element is not visible in the type of |PF [a]|. Instead,
we can add a new functor type to hold the elements, and parametrize
all functors by the element type:

\begin{code}
data K a        e (r :: * -> *) = K a
data E          e (r :: * -> *) = E e
data I          e (r :: * -> *) = I (r e)
data (f :+: g)  e (r :: * -> *) = L (f e r) | R (g e r)
data (f :*: g)  e (r :: * -> *) = f e r :*: g e r
\end{code}
%if style == newcode
\begin{code}
infixr 7 :*:
infixr 6 :+:
\end{code}
%endif

We can now represent the list:

\begin{code}
type family (PF (a :: * -> *)) :: * -> (* -> *) -> *

type instance (PF []) = K () :+: E :*: I

fromList  :: [a] -> PF [] a []
fromList []        = L (K ())
fromList (x : xs)  = R (E x :*: I xs)

toList    :: PF [] a [] -> [a]
toList (L (K ()))          = []
toList (R (E x :*: I xs))  = x : xs
\end{code}

To allow the definition of generic functions, we create a type class
for all types that have a pattern functor representation. This type
class contains two functions: one converting from the original data
type to the pattern functor, and one from the pattern functor back to
the original type. Making the list type an instance of this type class
is trivial, because we already defined the conversion functions above:
|fromList| and |toList|.

\begin{code}
class Ix f where
    from  :: f e       -> PF f e f
    to    :: PF f e f  -> f e

instance Ix [] where
    from  = fromList
    to    = toList
\end{code}

Note that we are now only describing data types of kind |* -> *|.
While it is possible to represent a data type without elements in this
view, it means adding a (superfluous) type parameter to the data type.
Furthermore, if we want to represent a data type with two different
element types, for example a tree with one type of value in the
branches and another in the leaves, we cannot do it in this
representation. We would have to expand our functor universe again,
adding a second type for elements, and extending the kind of the data
types we represent to |* -> * -> *|.

\subsection{Generic map}

To define a generic map functor, we define a type class |GMap|. We
make all functors instance of this type class. When the pattern
functor of a type is an instance of this type class, we can map over
the original type by converting to the pattern functor, mapping over
that, and converting back.

The type class |GMap| contains one function, |gmap'|. The second
argument to this function, is the function you want to apply to all
elements in the functor (the third argument). The first argument is a
function that we can apply to the recursive points. This is needed
because our conversion to functors is only one level deep: at the
recursive points, values of the original data type are stored, and we
have to be able to convert these as well. Later, in the top level
function |gmap|, we will ``tie the knot'' so that the user doesn't
have to provide this function.

\begin{code}
class GMap f where
    gmap' :: (r a -> r b) -> (a -> b) -> f a r -> f b r
\end{code}

We give instances of this class for all our functors. For |K|, we do
nothing, and for |I|, we apply the first argument to the recursive
structure contained within. In the |E| case, we do the actual work,
applying the function being mapped to an element. For the sum and
product, we just propagate the function call to the next level.

\begin{code}
instance GMap (K a) where
    gmap' _ _ (K a) = (K a)

instance GMap I where
    gmap' rf _ (I r) = I (rf r)

instance GMap E where
    gmap' _ f (E x) = E (f x)

instance (GMap f, GMap g) => GMap (f :+: g) where
    gmap' rf f (L x) = L (gmap' rf f x)
    gmap' rf f (R x) = R (gmap' rf f x)

instance (GMap f, GMap g) => GMap (f :*: g) where
    gmap' rf f (x :*: y) = gmap' rf f x :*: gmap' rf f y
\end{code}

Now we can define a generic map function. If a type is an instance of
|Ix|, i.e. it can be converted to a pattern functor, and this pattern
functor is an instance of |GMap| (which it will be if it is
constructed from our standard functors), we can map over it. We do
this by first converting from the original data type to the pattern
functor, mapping over that with |gmap'|, and converting the result
back to the original data type. Here, we also supply the function to
apply at the recursive points: |gmap f|. Note that we could not apply
|gmap f| to |r| in the instance for |I|, since there we could not
satisfy the |Ix r| and |GMap (PF r)| constraints, because |r| is
universally quantified in the class method |gmap'|.

\begin{code}
gmap :: (Ix r, GMap (PF r)) => (a -> b) -> r a -> r b
gmap f = to . gmap' (gmap f) f . from
\end{code}

We can now use |gmap| on any type for which we have a generic
representation. Since we have defined an |Ix| instance for lists
earlier, we can now evaluate |gmap (+1) [1,2,3]| to get \eval{gmap
(+1) [1,2,3]}.

We have extended the functor representation from Section
\ref{sec:functorrep} to be able to represent data types with one type
parameter. However, to represent types with no type parameters, we
have to wrap them, since we can only represent data types of kind |*
-> *|. We also cannot represent data types with more than one type
parameter, like the |Either| type, except by representing the first
type parameter using the |K| constructor. If we do this we once again
use the ability to use this element value in generic functions.

The approach of using functors of kind |* -> *| to represent data
types with one type parameter has been used before, for example in
PolyP \cite{polyp}.  Other generic programming approaches also use
representations of different arities to represent data types with
different numbers of type parameters. While this approach does work,
it means that separate generic machinery has to be implemented for
each number of type parameters.
