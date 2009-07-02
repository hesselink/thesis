\section{Abstract indices}
%include polycode.fmt
%include forall.fmt
%format family = "\mathbf{family}"
%if style /= newcode
%format :+: = "\oplus"
%format :*: = "\otimes"
%format :>: = "\rhd"
%format ~ = "\sim"
%format phi = "\phi"
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
           , TypeSynonymInstances
           , ScopedTypeVariables
           #-}
\end{code}
%endif

% This code is the same as in the previous section, so it is not shown
% in the pdf.
%if style == newcode
\begin{code}
data K a        (r :: * -> *) ix = K a
data I xi       (r :: * -> *) ix = I (r xi)
data (f :+: g)  (r :: * -> *) ix = L (f r ix) | R (g r ix)
data (f :*: g)  (r :: * -> *) ix = f r ix :*: g r ix

infixr 6 :+:
infixr 8 :*:

data (f :>: xi)  (r :: * -> *) ix where
  Tag :: f r ix -> (f :>: ix) r ix

data Expr  =  Const Int
           |  Add Expr Expr
           |  Mul Expr Expr
           |  EVar Var
           |  Let Decl Expr

data Decl  =  Var := Expr
           |  Seq Decl Decl

type Var   =  String
\end{code}
%endif

change indices and tags.

\begin{code}
data Zero
data Suc a

type PFAST  =    (    K Int
                 :+:  I Zero  :*: I Zero
                 :+:  I Zero  :*: I Zero
                 :+:  I (Suc (Suc Zero))
                 :+:  I (Suc Zero)  :*: I Zero
                 ) :>: Zero
            :+:  (    I (Suc (Suc Zero))   :*: I Zero
                 :+:  I (Suc Zero)  :*: I (Suc Zero) 
                 ) :>: (Suc Zero)
            :+:       K String :>: (Suc (Suc Zero))
\end{code}

Change AST to relation.

\begin{code}
data AST :: * -> * -> * where
  Expr :: AST Expr Zero
  Decl :: AST Decl (Suc Zero)
  Var  :: AST Var (Suc (Suc Zero))
\end{code}

\begin{code}
type family PF phi :: (* -> *) -> * -> *
type instance PF AST = PFAST
\end{code}

change wrapper to existential with relation.

\begin{code}
data R0 :: (* -> * -> *) -> * -> * where
  R0 :: phi a ix -> a -> R0 phi ix

class Fam phi where
  from  ::  phi a ix  -> a            -> PF phi (R0 phi) ix
  to    ::  phi a ix  -> PF phi (R0 phi) ix -> a
\end{code}

change to use R0.

\begin{code}
instance Fam AST where
  from  Expr  (Const i)    = L (Tag (L (K i)))
  from  Expr  (Add e1 e2)  = L (Tag (R (L (I (R0 Expr e1) :*: I (R0 Expr e2)))))
  from  Expr  (Mul e1 e2)  = L (Tag (R (R (L (I (R0 Expr e1) :*: I (R0 Expr e2))))))
  from  Expr  (EVar s)     = L (Tag (R (R (R (L (I (R0 Var s)))))))
  from  Expr  (Let d e)    = L (Tag (R (R (R (R (I (R0 Decl d) :*: I (R0 Expr e)))))))
  from  Decl  (s := e)     = R (L (Tag (L (I (R0 Var s) :*: I (R0 Expr e)))))
  from  Decl  (Seq d1 d2)  = R (L (Tag (R (I (R0 Decl d1) :*: I (R0 Decl d2)))))
  from  Var   s            = R (R (Tag (K s)))
  to    Expr  (L (Tag (L (K i))))                                = Const i
  to    Expr  (L (Tag (R (L (I (R0 Expr e1) :*: I (R0 Expr e2))))))        = Add e1 e2
  to    Expr  (L (Tag (R (R (L (I (R0 Expr e1) :*: I (R0 Expr e2)))))))    = Mul e1 e2
  to    Expr  (L (Tag (R (R (R (L (I (R0 Var s))))))))               = EVar s
  to    Expr  (L (Tag (R (R (R (R (I (R0 Decl d) :*: I (R0 Expr e))))))))  = Let d e
  to    Decl  (R (L (Tag (L (I (R0 Var s) :*: I (R0 Expr e))))))          = s := e
  to    Decl  (R (L (Tag (R (I (R0 Decl d1) :*: I (R0 Decl d2))))))        = Seq d1 d2
  to    Var   (R (R (Tag (K s))))                                = s
\end{code}

\begin{code}
class HFunctor phi f where
  hmap :: (forall ix. phi ix -> r ix -> r' ix) -> f r ix -> f r' ix
\end{code}

Add existential wrapper to change relation to proof.

\begin{code}
data Proof :: (* -> * -> *) -> * -> * where
  Proof :: phi a ix -> Proof phi ix

class El phi ix where
  proof :: phi ix
\end{code}

Change proofs to abstract indices and wrapper.

\begin{code}
instance El (Proof AST) Zero  where proof = Proof Expr
instance El (Proof AST) (Suc Zero)  where proof = Proof Decl
instance El (Proof AST) (Suc (Suc Zero))   where proof = Proof Var
\end{code}

No changes!

\begin{code}
instance HFunctor phi (K a) where
  hmap _ (K x) = K x

instance El phi xi => HFunctor phi (I xi) where
  hmap f (I r) = I (f proof r)

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :+: g) where
  hmap f (L x)  = L  (hmap f x)
  hmap f (R y)  = R  (hmap f y)

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :*: g) where
  hmap f (x :*: y) = hmap f x :*: hmap f y

instance HFunctor phi f => HFunctor phi (f :>: xi) where
  hmap f (Tag x) = Tag (hmap f x)
\end{code}

Change to use R0. Need scoped type vars and Proof type.

\begin{code}
compos :: forall phi a ix. (Fam phi, HFunctor (Proof phi) (PF phi)) => (forall a ix. phi a ix -> a -> a) -> phi a ix -> a -> a
compos f p = to p . hmap rec . from p
  where
    rec :: forall ix. Proof phi ix -> R0 phi ix -> R0 phi ix
    rec _ (R0 p x) = R0 p (f p x)
\end{code}
