\section{Multirec: mutually recursive datatypes}
%include polycode.fmt
%include forall.fmt
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%format ~ = "\sim"
%format undefined = "\bot"
%options ghci -fglasgow-exts
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
\end{code}
%endif

The functor representation used in section \ref{sec:functorrep} and
beyond can only represent \emph{regular datatypes}. In particular, it
cannot represent a family of mutually recursive datatypes. This is
unfortunate, as these occur frequently in practice. 

The approach used in the multirec library \cite{multirec} still uses a
functor representation, but it can represent families of mutually
recursive datatypes.  It does this by \emph{indexing} the recursive
points with a type that indicated to which type in the family the
recursion goes.

Consider the following functor types:

\begin{code}
data K a        (r :: * -> *) ix = K a
data I xi       (r :: * -> *) ix = I (r xi)
data (f :+: g)  (r :: * -> *) ix = L (f r ix) | R (g r ix)
data (f :*: g)  (r :: * -> *) ix = f r ix :*: g r ix
\end{code}

The |K|, |(:+:)| and |(:*:)| functors now take an indexed recursive
type, and are indexed themselves, but are otherwise unchanged. The
interesting change is in the |I| type. It takes an extra type
parameter |xi|, which indicates which type to recurse on. Note that it
differs from the functor index |ix|, which indicates which type we are
currently describing.

As an example, let us consider a datatype of expressions, also used in
\cite{multirec}:

\begin{code}
data Expr  =  Const Int
           |  Add Expr Expr
           |  Mul Expr Expr
           |  EVar Var
           |  Let Decl Expr

data Decl  =  Var := Expr
           |  Seq Decl Decl

type Var   =  String
\end{code}

These datatypes are mutually recursive: |Expr| can contain a |Decl|,
and |Decl| can contain an |Expr|. Both contain |Var|s. To represent
this data type, we can use the following pattern functor:

\begin{code}
type PFAST = ()
         :+: ()
         :+: K String
\end{code}
