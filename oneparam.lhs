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

Note that we are now only describing data types of kind |* -> *|.
While it is possible to represent data type without elements in this
view, it means adding a (phantom) type parameter to the data type.
Furthermore, if we want to represent a data type with two different
element types, for example a tree with one type of value in the
branches and another in the leaves, we cannot do it in this
representation. We would have to expand our functor universe again,
adding a second type for elements, and extending the kind of the data
types we represent to |* -> * -> *|.

