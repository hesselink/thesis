\section{Arbitrary number of type parameters}
%include polycode.fmt
%include forall.fmt
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%format ~ = "\sim"
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
           , ScopedTypeVariables
           , FlexibleInstances
           #-}
\end{code}
%endif

\begin{code}
data Left a
data Right a
type Elem = Left
type Rec  = Right

data Case :: (* -> *) -> (* -> *) -> (* -> *) where
  CL :: l ix -> Case l r (Left  ix)
  CR :: r ix -> Case l r (Right ix)

data K a        (r :: * -> *) = K a
data I ix       (r :: * -> *) = I (r ix)
data (f :*: g)  (r :: * -> *) = f r :*: g r
data (f :+: g)  (r :: * -> *) = L (f r) | R (g r)
data I0 a ix = I0 { unI0 :: a }
\end{code}
%if style == newcode
\begin{code}
infixr 7 :*:
infixr 6 :+:
\end{code}
%endif

\begin{code}
data Zero
data Suc a

data (t :|: ts) :: * -> * where
  Z :: t     -> (t :|: ts) Zero
  S :: ts n  -> (t :|: ts) (Suc n)

infixr 8 :|:

data Nil a = Nil { magic :: forall a. a }
\end{code}

\begin{code}
data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b) deriving Show
\end{code}

\begin{code}
type family PF a :: (* -> *) -> *

type instance (PF (Tree a b)) = I (Elem Zero) :+: I (Rec Zero) :*: I (Elem (Suc Zero)) :*: I (Rec Zero)
\end{code}

\begin{code}
fromTree  :: Tree a b -> PF (Tree a b) (Case (a :|: b :|: Nil) (I0 (Tree a b)))
fromTree (Leaf a)        = L (I (CL (Z a)))
fromTree (Branch l b r)  = R (I (CR (I0 l)) :*: I (CL (S (Z b))) :*: I (CR (I0 r)))

toTree    :: PF (Tree a b) (Case (a :|: b :|: Nil) (I0 (Tree a b))) -> Tree a b
toTree (L (I (CL (Z a))))                                          = Leaf a
toTree (R (I (CR (I0 l)) :*: I (CL (S (Z b))) :*: I (CR (I0 r))))  = Branch l b r
\end{code}

\subsection{Generic map}

\begin{code}
class Ix a where
    type Es a :: * -> *
    from  :: a          -> PF a (Case (Es a) (I0 a))
    to    :: PF a (Case (Es a) (I0 a))  -> a

instance Ix (Tree a b) where
    type Es (Tree a b) = a :|: b :|: Nil
    from  = fromTree
    to    = toTree
\end{code}

\begin{code}
class HFunctor f where
    hmap :: (forall ix. r ix -> r' ix) -> f r -> f r'

instance HFunctor (K x) where
    hmap _ (K x) = (K x)

instance HFunctor (I ix) where
    hmap f (I x) = I (f x)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
    hmap f (L x) = L (hmap f x)
    hmap f (R x) = R (hmap f x)

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
    hmap f (x :*: y) = hmap f x :*: hmap f y

(<?>) :: (forall ix. l ix -> l' ix) -> (forall ix. r ix -> r' ix) -> Case l r ix -> Case l' r' ix
(f <?> g) (CL x) = CL (f x)
(f <?> g) (CR y) = CR (g y)

infix 8 <?>

gmap :: forall es es' a b. (Ix a, Ix b, HFunctor (PF a), PF a ~ PF b) => (forall n. Es a n -> Es b n) -> a -> b
gmap f = to . hmap (f <?> I0 . gmap f . unI0) . from

class Apply fs es where
  type Res fs es :: * -> *
  apply :: fs -> es n -> Res fs es n

instance (a ~ a', Apply fs es) => Apply (a -> b, fs) (a' :|: es) where
  type Res (a -> b, fs) (a' :|: es) = b :|: Res fs es
  apply (f, fs) (Z x) = Z (f x)
  apply (f, fs) (S x) = S (apply fs x)

instance (a ~ a') => Apply (a -> b) (a' :|: Nil) where
  type Res (a -> b) (a' :|: Nil) = b :|: Nil
  apply f (Z x) = Z (f x)
  apply f (S x) = magic x

(&) = (,)
infixr 5 &
\end{code}

\begin{code}
tree1 :: Tree Int String
tree1 = Branch (Leaf 1) "abc" (Branch (Leaf 2) "defg" (Leaf 3))

tree2 :: Tree Bool Int
tree2 = gmap (apply (even & length)) tree1
\end{code}

\begin{code}
class GZero prf f where
  gzero :: (forall ix. prf ix -> r ix) -> Bool -> f r

class Small x where
  small :: x

instance Small x => GZero prf (K x) where
  gzero _ _ = K small

class El prf ix where
  proof :: prf ix

instance (El prf ix) => GZero prf (I ix) where
  gzero f left = I (f proof)

instance (GZero prf f, GZero prf g) => GZero prf (f :+: g) where
  gzero f True   = L (gzero f True)
  gzero f False  = R (gzero f False)

instance (GZero prf f, GZero prf g) => GZero prf (f :*: g) where
  gzero f left = gzero f left :*: gzero f left

data CasePrf pl pr :: * -> * where
  PL :: pl ix -> CasePrf pl pr (Left ix)
  PR :: pr ix -> CasePrf pl pr (Right ix)

data NatPrf :: * -> * where
  PZ :: NatPrf Zero
  PS :: NatPrf n -> NatPrf (Suc n)

data IdPrf ix = IdPrf

class SmallEl prf es where
  smallEl :: prf ix -> es ix

instance (Small a, SmallEl NatPrf as) => SmallEl NatPrf (a :|: as) where
  smallEl PZ      = Z small
  smallEl (PS p)  = S (smallEl p)

instance SmallEl NatPrf Nil where
  smallEl p = undefined

gencase :: (forall ix. pl ix -> l ix) -> (forall ix. pr ix -> r ix) -> CasePrf pl pr ix -> Case l r ix
gencase f g (PL p) = CL (f p)
gencase f g (PR p) = CR (g p)

gleft :: forall a. (Ix a, GZero (CasePrf NatPrf IdPrf) (PF a), SmallEl NatPrf (Es a)) => a
gleft = to (gzero rec True)
  where
    rec :: forall ix. CasePrf NatPrf IdPrf ix -> Case (Es a) (I0 a) ix
    rec = smallEl `gencase` const (I0 gleft)

instance Small Int where
  small = 0

instance Small [a] where
  small = []

instance El NatPrf Zero where
  proof = PZ

instance El NatPrf n => El NatPrf (Suc n) where
  proof = PS proof

instance El IdPrf ix where
  proof = IdPrf

instance (El pl ix) => El (CasePrf pl pr) (Left ix) where
  proof = PL proof

instance (El pr ix) => El (CasePrf pl pr) (Right ix) where
  proof = PR proof
\end{code}
