\section{Multirec with type parameters}
%include polycode.fmt
%include forall.fmt
%if style /= newcode
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%format ~ = "\sim"
%endif
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

\Todo{why does gmap need two proofs, not one? Why does zipwith need two proofs, not three (or one)?}
