\section{Multirec with type parameters}
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

\begin{code}
data Left ix
data Right ix

data Case :: (* -> *) -> (* -> *) -> (* -> *) where
  CL  :: l  ix -> Case l r (Left   ix)
  CR  :: r  ix -> Case l r (Right  ix)
\end{code}

\begin{code}
data K a        (r :: * -> *) ix = K a
data I xi       (r :: * -> *) ix = I (r xi)
data (f :+: g)  (r :: * -> *) ix = L (f r ix) | R (g r ix)
data (f :*: g)  (r :: * -> *) ix = f r ix :*: g r ix

infixr 6 :+:
infixr 8 :*:

data (f :>: xi)  (r :: * -> *) ix where
  Tag :: f r ix -> (f :>: ix) r ix

data Expr a  =  Const a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  EVar Var
             |  Let (Decl a) (Expr a)

data Decl a  =  Var := (Expr a)
             |  Seq (Decl a) (Decl a)

type Var     =  String
\end{code}

\begin{code}
data Zero
data Suc a
type Elem  = Left
type Rec   = Right

type PFAST  =    (    I (Elem Zero)
                 :+:  I (Rec Zero)        :*: I (Rec Zero)
                 :+:  I (Rec Zero)        :*: I (Rec Zero)
                 :+:  I (Rec (Suc (Suc Zero)))
                 :+:  I (Rec (Suc Zero))  :*: I (Rec Zero)
                 ) :>: Zero
            :+:  (    I (Rec (Suc (Suc Zero)))  :*: I (Rec Zero)
                 :+:  I (Rec (Suc Zero))        :*: I (Rec (Suc Zero)) 
                 ) :>: (Suc Zero)
            :+:       K String :>: (Suc (Suc Zero))
\end{code}
\begin{code}
data E0 a ix = E0 { unE0 :: a }

data AST :: (* -> *) -> * -> * -> * where
  Expr  :: AST (E0 a) (Expr a)  Zero
  Decl  :: AST (E0 a) (Decl a)  (Suc Zero)
  Var   :: AST (E0 a) Var       (Suc (Suc Zero))

type family PF (phi :: (* -> *) -> * -> * -> *) :: (* -> *) -> * -> *
type instance PF AST = PFAST
\end{code}
\begin{code}
data R0 :: ((* -> *) -> * -> * -> *) -> (* -> *) -> * -> * where
  R0 :: phi es a ix -> a -> R0 phi es ix

class Fam phi es where
  from  ::  phi es a ix  -> a                                -> PF phi (Case es (R0 phi es)) ix
  to    ::  phi es a ix  -> PF phi (Case es (R0 phi es)) ix  -> a

rec p  x = I (CR  (R0 p x))
el     x = I (CL  (E0 x))

instance Fam AST (E0 a) where
  from  Expr  (Const i)    = L (Tag (L (el i)))
  from  Expr  (Add e1 e2)  = L (Tag (R (L (rec Expr e1 :*: rec Expr e2))))
  from  Expr  (Mul e1 e2)  = L (Tag (R (R (L (rec Expr e1 :*: rec Expr e2)))))
  from  Expr  (EVar s)     = L (Tag (R (R (R (L (rec Var s))))))
  from  Expr  (Let d e)    = L (Tag (R (R (R (R (rec Decl d :*: rec Expr e))))))
  from  Decl  (s := e)     = R (L (Tag (L (rec Var s :*: rec Expr e))))
  from  Decl  (Seq d1 d2)  = R (L (Tag (R (rec Decl d1 :*: rec Decl d2))))
  from  Var   s            = R (R (Tag (K s)))
  to    Expr  (L (Tag (L (I (CL (E0 i))))))
                           = Const i
  to    Expr  (L (Tag (R (L (I (CR (R0 Expr e1)) :*: I (CR (R0 Expr e2)))))))
                           = Add e1 e2
  to    Expr  (L (Tag (R (R (L (I (CR (R0 Expr e1)) :*: I (CR (R0 Expr e2))))))))
                           = Mul e1 e2
  to    Expr  (L (Tag (R (R (R (L (I (CR (R0 Var s)))))))))
                           = EVar s
  to    Expr  (L (Tag (R (R (R (R (I (CR (R0 Decl d)) :*: I (CR (R0 Expr e)))))))))
                           = Let d e
  to    Decl  (R (L (Tag (L (I (CR (R0 Var s)) :*: I (CR (R0 Expr e)))))))
                           = s := e
  to    Decl  (R (L (Tag (R (I (CR (R0 Decl d1)) :*: I (CR (R0 Decl d2)))))))
                           = Seq d1 d2
  to    Var   (R (R (Tag (K s))))
                           = s

\end{code}
\begin{code}
data Proof :: (* -> * -> *) -> * -> * where
  Proof :: phi a ix -> Proof phi ix

class El phi ix where
  proof :: phi ix

instance El (Proof (AST (E0 a)))  Zero              where proof = Proof Expr
instance El (Proof (AST (E0 a)))  (Suc Zero)        where proof = Proof Decl
instance El (Proof (AST (E0 a)))  (Suc (Suc Zero))  where proof = Proof Var

data NatPrf :: * -> * where
  PZ :: NatPrf Zero
  PS :: NatPrf n -> NatPrf (Suc n)

instance El NatPrf Zero where
  proof = PZ

instance El NatPrf a => El NatPrf (Suc a) where
  proof = PS proof

instance El pl ix => El (Case pl pr) (Left ix) where
  proof = CL proof

instance El pr ix => El (Case pl pr) (Right ix) where
  proof = CR proof

type FamPrf phi (es :: * -> *) = Case NatPrf (Proof (phi es))
\end{code}

\begin{code}
class HFunctor phi f where
  hmap :: (forall ix. phi ix -> r ix -> r' ix) -> f r ix -> f r' ix

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
\begin{code}
(<?>) :: (forall ix. prf   ix -> f  ix -> f'  ix) ->
         (forall ix. prf'  ix -> g  ix -> g'  ix) ->
         Case prf prf' ix -> Case f g ix -> Case f' g' ix
(f <?> g) (CL p) (CL x) = CL (f p x)
(f <?> g) (CR p) (CR y) = CR (g p y)

compos ::  forall phi es a ix. (Fam phi es, HFunctor (FamPrf phi es) (PF phi)) => 
           (forall a ix. phi es a ix -> a -> a) -> phi es a ix -> a -> a
compos f p = to p . hmap (el <?> rec) . from p
  where
    el  :: forall ix. NatPrf ix -> es ix -> es ix
    el  = const id
    rec :: forall ix. Proof (phi es) ix -> R0 phi es ix -> R0 phi es ix
    rec _ (R0 p x) = R0 p (f p x)

gmap ::  forall phi es es' a b ix. (Fam phi es, Fam phi es', HFunctor (FamPrf phi es') (PF phi)) =>
         (forall ix. es ix -> es' ix) -> phi es a ix -> phi es' b ix -> a -> b
gmap f pfrom pto = to pto . hmap (el <?> rec) . from pfrom
  where
    el :: forall ix. NatPrf ix -> es ix -> es' ix
    el = const f
    rec :: forall ix. Proof (phi es') ix -> R0 phi es ix -> R0 phi es' ix
    rec (Proof pto) (R0 pfrom x) = R0 pto (gmap f pfrom pto x)

\end{code}
\begin{code}
renameVar :: Num a => Expr a -> Expr a
renameVar = renameVar' Expr
  where
    renameVar' :: Num a => AST (E0 a) b ix -> b -> b
    renameVar' Var  s          = s ++ "_"
    renameVar' Expr (Const i)  = Const (i + 1)
    renameVar' p    x          = compos renameVar' p x
\end{code}
