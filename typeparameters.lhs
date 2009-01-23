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
or a recursive position. We can also write conversion functions to and
from the pattern functor:

\begin{code}
fromNat  :: Nat -> PF Nat Nat
fromNat Zero     = L (K ())
fromNat (Suc n)  = R (I n)
toNat    :: PF Nat Nat -> Nat
toNat (L (K ()))  = Zero
toNat (R (I n))   = Suc n
\end{code}

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
data I          e (r :: * -> *) = I (r e)
data (f :+: g)  e (r :: * -> *) = L (f e r) | R (g e r)
data (f :*: g)  e (r :: * -> *) = f e r :*: g e r
\end{code}

We can now represent the list:

\begin{code}
type family (PF a) :: * -> (* -> *) -> *

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

\section{Arbitrary number of type parameters}

What we want to do, is abstract over the number of type parameters a
type former takes. This means also abstracting over the kind of the
recursive positions. The idea is, to use numbers on the type level to
indicate the number of type parameters, and to indicate which type
parameter an element corresponds to.

In a dependently typed programming language, we can apply this idea
directly. [TODO: How do I insert Agda code in here?]

In Haskell, we can represent this as follows: we hide the type of the
parameter in the |E| constructor, using existential quantification. We
define a GADT that allows us to recover this type by pattern matching,
and we parametrize all functors by this GADT. The functors now become:

\begin{code}
data K a        (es :: * -> * -> *) r = K a
data E a        (es :: * -> * -> *) r where
    E :: (es a e) -> e -> E a es r
data I          (es :: * -> * -> *) r = I r
data (f :*: g)  (es :: * -> * -> *) r = f es r :*: g es r
data (f :+: g)  (es :: * -> * -> *) r = L (f es r) | R (g es r)
\end{code}

Notice that the type |e| of the parameter in the |E| constructor is
not visible in its type, |E a es r|. However, it is visible in the
type of the GADT that is stored with it. This allows recovery of the
type by pattern matching. The type |a| in the type of |E| is the type
level number, used to indicate which type parameter it is. This is
needed to ensure that we don't change the order of the parameters.
[TODO: clear up, example].

As an example of the GADT that is stored with the parameters, let's
consider representing a data type with two type parameters. The GADT
will be as follows:

\begin{code}
data Zero
data Suc a

data ParamS2 :: * -> * -> * -> * -> *  where
    Param1 :: ParamS2 a b Zero        a
    Param2 :: ParamS2 a b (Suc Zero)  b
\end{code}

In essence, this is a type level function, taking |Zero| to type |a|,
and |Suc Zero| to type |b|. In the type of the functors, |a| and |b|
have been instantiated to concrete types by partially applying
|ParamS2|, since it needs to have kind |* -> * -> *| there.

As a concrete example, consider a tree data type that stores one type
of value in its leaves, and another in the branches:

\begin{code}
data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b)
\end{code}

We define a type family, and make an instance for |Tree|:

\begin{code}
type family PF a :: (* -> * -> *) -> * -> *

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I
\end{code}

In the `from' function, we bundle up one of the constructors of the
|ParamS2| type with the actual parameter value. In the `to' function,
we pattern match on the GADT, which allows us to return the correct
type again.

\begin{code}
fromTree  :: Tree a b -> PF (Tree a b) (ParamS2 a b) (Tree a b)
fromTree (Leaf a)        = L (E Param1 a)
fromTree (Branch l b r)  = R (I l :*: E Param2 b :*: I r)
toTree    :: PF (Tree a b) (ParamS2 a b) (Tree a b) -> Tree a b
toTree (L (E Param1 a))                  = Leaf a
toTree (R (I l :*: E Param2 b :*: I r))  = Branch l b r
\end{code}
