\chapter{Arbitrary number of type parameters}
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

\section{Functor representation}
A simple functor representation of data types uses four different data types:

\begin{code}
data K a        r = K a
data I          r = I r
data (f :+: g)  r = L (f r) | R (g r)
data (f :*: g)  r = f r :*: g r
\end{code}

The first represents types that we do not include in the generic
representation. This means that from the functor point of view, they
are constants. The second represent the recursive positions in the
data type. The third and fourth represent sums and products,
respectively.

To construct a pattern functor for a specific data type, you would
construct one out of these base functors. For example, if we define
Peano-style numerals:

\begin{code}
data Nat = Zero | Suc Nat
\end{code}

Now we can define a type family for pattern functors, and give an
instance for the |Nat| data type:

\begin{code}
type family (PF a) :: * -> *

type instance PF Nat = K () :+: I
\end{code}

Here, we represent the data type as the sum of two constructors: a
constant |()| (sometimes an extra base functor |U| is used for this)
or a recursive position.

\section{Type parameters}

Using this representation to represent types with type parameters,
like |[a]|, is problematic. For example, let's say we want to
represent the list datatype, which might be defined as:

%if style /= newcode
\begin{code}
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
data I          e (r :: * -> *) = I r
data (f :+: g)  e (r :: * -> *) = L (f e r) | R (g e r)
data (f :*: g)  e (r :: * -> *) = f e r :*: g e r
\end{code}

We can now represent the list:

\begin{code}
type instance (PF []) = K () :+: E :*: I
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
