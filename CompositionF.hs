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
           #-}
module CompositionF where

data E                 (r :: * -> (* -> *) -> *) e (ix :: * -> *) = E {unE :: e}
data K a               (r :: * -> (* -> *) -> *) e (ix :: * -> *) = K a
data I (xi :: * -> *)  (r :: * -> (* -> *) -> *) e (ix :: * -> *) = I { unI :: (r e xi) }
data (f :+: g)         (r :: * -> (* -> *) -> *) e (ix :: * -> *) = L (f r e ix) | R (g r e ix)
data (f :*: g)         (r :: * -> (* -> *) -> *) e (ix :: * -> *) = f r e ix :*: g r e ix

infixr 6 :+:
infixr 8 :*:

data (f :>: (xi :: * -> *))  (r :: * -> (* -> *) -> *) e (ix :: * -> *) where
  Tag :: f r e ix -> (f :>: ix) r e ix

type family PF phi :: (* -> (* -> *) -> *) -> * -> (* -> *) -> *

data I0 e a = I0 { unI0 :: a e }

class Fam phi where
  from  ::  phi e ix  -> ix e            -> PF phi I0 e ix
  to    ::  phi e ix  -> PF phi I0 e ix  -> ix e

class HFunctor (phi :: * -> (* -> *) -> *) (f :: (* -> (* -> *) -> *) -> * -> (* -> *) -> *) where
  hmap :: (forall ix. phi e ix -> r e ix -> r' e ix) -> f r e ix -> f r' e ix

class El phi (ix :: * -> *) where
  proof :: phi e ix

instance HFunctor phi (K a) where
  hmap _ (K x) = K x

instance HFunctor phi E where
  hmap _ (E x) = E x

instance El phi xi => HFunctor phi (I xi) where
  hmap f (I r) = I (f proof r)

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :+: g) where
  hmap f (L x)  = L  (hmap f x)
  hmap f (R y)  = R  (hmap f y)

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :*: g) where
  hmap f (x :*: y) = hmap f x :*: hmap f y

instance HFunctor phi f => HFunctor phi (f :>: xi) where
  hmap f (Tag x) = Tag (hmap f x)

compos :: (Fam phi, HFunctor phi (PF phi)) => (forall ix. phi e ix -> ix e -> ix e) -> phi e ix -> ix e -> ix e
compos f p = to p . hmap (\p -> I0 . f p . unI0) . from p


class GMap (phi :: * -> (* -> *) -> *) (f :: (* -> (* -> *) -> *) -> * -> (* -> *) -> *) where
  gmapF :: (forall ix. phi e ix -> phi e' ix -> r e ix -> r e' ix) -> phi e ix -> phi e' ix -> (e -> e') -> f r e ix -> f r e' ix

instance GMap phi (K a) where
  gmapF _ _ _ _ (K x) = K x

instance GMap phi E where
  gmapF _ _ _ g (E x) = E (g x)

instance El phi xi => GMap phi (I xi) where
  gmapF f _ _ _ (I x) = I (f proof proof x)

instance (GMap phi f, GMap phi g) => GMap phi (f :+: g) where
  gmapF f pf pt g (L x) = L (gmapF f pf pt g x)
  gmapF f pf pt g (R y) = R (gmapF f pf pt g y)

instance (GMap phi f, GMap phi g) => GMap phi (f :*: g) where
  gmapF f pf pt g (x :*: y) = gmapF f pf pt g x :*: gmapF f pf pt g y

instance GMap phi f => GMap phi (f :>: xi) where
  gmapF f pf pt g (Tag x) = Tag (gmapF f pf pt g x)

gmap :: (Fam phi, GMap phi (PF phi)) => phi a ix -> phi b ix -> (a -> b) -> ix a -> ix b
gmap pfrom pto f x = to pto (gmapF (gmapI0 f) pfrom pto f (from pfrom x))

gmapI0 :: (Fam phi, GMap phi (PF phi)) => (a -> b) -> phi a ix -> phi b ix -> I0 a ix -> I0 b ix
gmapI0 f pfrom pto (I0 x) = I0 (gmap pfrom pto f x)
