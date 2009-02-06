\section{Type parameters}
\long\def\ignore#1{}
%include polycode.fmt
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%if style == newcode
\begin{code}
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , FlexibleContexts
           #-}
\end{code}
%endif

Using this representation to represent types with type parameters,
like |[a]|, is problematic. For example, let's say we want to
represent the list datatype, which might be defined as:

%This is a nasty hack, but it works.
%format % = " "
%if style /= newcode
\begin{code}%
data [a] = [] | a : [a]
\end{code}
%endif

If we try to represent this in our view, we have to use |K| for the
elements. However, this means that it is not possible to define
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
While it is possible to represent data type without elements in this
view, it means adding a (phantom) type parameter to the data type.
Furthermore, if we want to represent a data type with two different
element types, for example a tree with one type of value in the
branches and another in the leaves, we cannot do it in this
representation. We would have to expand our functor universe again,
adding a second type for elements, and extending the kind of the data
types we represent to |* -> * -> *|.

\subsection{Generic map}

To define a generic map functor, we define a type class |GMap|. We
make all functors instance of this type class. When the pattern
functor of a type is then an instance of this type class, we can map
over the original type by converting to the pattern functor, mapping
over that, and converting back.

The type class contains one function, |gmap'|. The second argument to
this function, is the function you want to apply to all elements in
the functor (the third argument). The first argument is a function
that we can apply to the recursive points. This is needed because our
conversion to functors is only one level deep: at the recursive
points, the original data type is stored, and we have to be able to
convert it as well. Later, in the top level function |gmap|, we will
``tie the knot'' so that the user doesn't have to provide this
function.

\begin{code}
class GMap f where
    gmap' :: (r a -> r b) -> (a -> b) -> f a r -> f b r
\end{code}

We can now give instances of this class for all our functors. For a
|K|, we do nothing, and for an |I|, we apply the first argument to the
recursive structure contained within. In the |E| case, we do the
actual work, applying the function being mapped to an element. For the
sum and product, we just propagate the function call to the next
level.

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
this in the instance for |I|, since there we could not satisfy the |Ix
r| and |GMap (PF r)| constraints, since |r| is universally quantified
in the class method |gmap'|.

\begin{code}
gmap :: (Ix r, GMap (PF r)) => (a -> b) -> r a -> r b
gmap f = to . gmap' (gmap f) f . from
\end{code}
