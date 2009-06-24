\section{Functor representation}
\label{sec:functorrep}
%include polycode.fmt
%if style /= newcode
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%endif
%if style == newcode
\begin{code}
{-# LANGUAGE TypeFamilies
           , TypeOperators
           #-}
\end{code}
%endif

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

