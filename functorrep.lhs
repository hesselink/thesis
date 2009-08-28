\section{Functor representation}
\label{sec:functorrep}
%include polycode.fmt
%include thesis.fmt
%if style == newcode
\begin{code}
{-# LANGUAGE TypeFamilies
           , TypeOperators
           #-}
\end{code}
%endif

Generic programming exists thanks to the fact that Haskell algebraic
datatypes have a generic structure. They are composed of \emph{sums}
(choices) of constructors, each consisting of \emph{products}
(combinations) of types. By creating a uniform representation of
datatypes using so-called functors to represent these sums and
products, we can treat datatypes generically.

In the \emph{fixed-point} view of a datatype, we use an additional
functor to represent the recursive points in a datatype. This allows
us to write generic functions that exploit knowledge about these
recursive points, like the |fold|.

This simple functor representation of data types uses four different
data types:

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

A pattern functor for a specific data type is expressed in terms of
these base functors. For example, consider Peano-style numerals:

\begin{code}
data Nat = Zero | Suc Nat
\end{code}

Now we can define a type family for pattern functors, and give an
instance for the |Nat| data type:

\begin{code}
type family (PF a) :: * -> *

type instance PF Nat = K () :+: I
\end{code}

We represent the data type as the sum of two constructors: a constant
|()| (sometimes an extra base functor |U| is used for this) or a
recursive position. We can also write conversion functions to and from
the pattern functor:

\begin{code}
fromNat  :: Nat -> PF Nat Nat
fromNat Zero     = L (K ())
fromNat (Suc n)  = R (I n)

toNat    :: PF Nat Nat -> Nat
toNat (L (K ()))  = Zero
toNat (R (I n))   = Suc n
\end{code}

