\section{Composition}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt
%if style /= newcode
%format CompanyU' = "CompanyU"
%format ldots = "\ldots"
%endif
%options ghci -fglasgow-exts
%if style == newcode
%format ldots = "-- "
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
           , UndecidableInstances
           , ScopedTypeVariables
           #-}
\end{code}

\begin{code}
import qualified CompositionF as F
import CompositionF (GMap)

data K a             (r :: kphi -> *) (ix :: kphi) = K a
data I (xi :: kphi)  (r :: kphi -> *) (ix :: kphi) = I { unI :: (r xi) }
data (f :+: g)       (r :: kphi -> *) (ix :: kphi) = L (f r ix) | R (g r ix)
data (f :*: g)       (r :: kphi -> *) (ix :: kphi) = f r ix :*: g r ix

infixr 6 :+:
infixr 8 :*:

data (f :>: (xi :: kphi))  (r :: kphi -> *) (ix :: kphi) where
  Tag :: f r ix -> (f :>: ix) r ix
type family PF phi :: (kphi -> *) -> kphi -> *

data I0 a = I0 { unI0 :: a }

class Fam phi where
  from  ::  phi ix  -> ix            -> PF phi I0 ix
  to    ::  phi ix  -> PF phi I0 ix  -> ix

class HFunctor phi f where
  hmap :: (forall ix. phi ix -> r ix -> r' ix) -> phi ix -> f r ix -> f r' ix

class El phi ix where
  proof :: phi ix

instance HFunctor phi (K a) where
  hmap _ _ (K x) = K x

instance El phi xi => HFunctor phi (I xi) where
  hmap f _ (I r) = I (f proof r)

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :+: g) where
  hmap f p (L x)  = L  (hmap f p x)
  hmap f p (R y)  = R  (hmap f p y)

instance (HFunctor phi f, HFunctor phi g) => HFunctor phi (f :*: g) where
  hmap f p (x :*: y) = hmap f p x :*: hmap f p y

instance HFunctor phi f => HFunctor phi (f :>: xi) where
  hmap f p (Tag x) = Tag (hmap f p x)

compos :: (Fam phi, HFunctor phi (PF phi)) => (forall ix. phi ix -> ix -> ix) -> phi ix -> ix -> ix
compos f p = to p . hmap (\p -> I0 . f p . unI0) p . from p

instance El CompanyU Company where
  proof = Company
instance El CompanyU [Dept] where
  proof = DeptList
instance El CompanyU Dept where
  proof = Dept
instance El CompanyU Employee where
  proof = Employee
instance El CompanyU [Unit] where
  proof = UnitList
instance El CompanyU Unit where
  proof = Unit
instance El CompanyU Person where
  proof = Person
instance El CompanyU Salary where
  proof = Salary

instance Fam CompanyU where
  from Company (C ds) = L (Tag (I (I0 ds)))
  from DeptList [] = R (L (Tag (K ())))
  from DeptList (d : ds) = R (R (L (Tag (I (I0 d) :*: I (I0 ds)))))
  from Dept (D n m us) = R (R (R (L (Tag (K n :*: I (I0 m) :*: I (I0 us))))))
  from UnitList [] = R (R (R (R (L (Tag (K ()))))))
  from UnitList (u : us) = R (R (R (R (R (L (Tag (I (I0 u) :*: I (I0 us))))))))
  from Unit (PU e) = R (R (R (R (R (R (L (Tag (I (I0 e)))))))))
  from Unit (DU d) = R (R (R (R (R (R (R (L (Tag (I (I0 d))))))))))
  from Employee (E p s) = R (R (R (R (R (R (R (R (L (Tag (I (I0 p) :*: I (I0 s)))))))))))
  from Person (P n a) = R (R (R (R (R (R (R (R (R (L (Tag (K n :*: K a)))))))))))
  from Salary (S s) = R (R (R (R (R (R (R (R (R (R (Tag (K s)))))))))))
  to Company (L (Tag (I (I0 ds)))) = C ds
  to DeptList (R (L (Tag (K ())))) = []
  to DeptList (R (R (L (Tag (I (I0 d) :*: I (I0 ds)))))) = d : ds
  to Dept (R (R (R (L (Tag (K n :*: I (I0 m) :*: I (I0 us))))))) = D n m us
  to UnitList (R (R (R (R (L (Tag (K ()))))))) = []
  to UnitList (R (R (R (R (R (L (Tag (I (I0 u) :*: I (I0 us))))))))) = u : us
  to Unit (R (R (R (R (R (R (L (Tag (I (I0 e)))))))))) = PU e
  to Unit (R (R (R (R (R (R (R (L (Tag (I (I0 d))))))))))) = DU d
  to Employee (R (R (R (R (R (R (R (R (L (Tag (I (I0 p) :*: I (I0 s)))))))))))) = E p s
  to Person (R (R (R (R (R (R (R (R (R (L (Tag (K n :*: K a)))))))))))) = P n a
  to Salary (R (R (R (R (R (R (R (R (R (R (Tag (K s)))))))))))) = S s

genCom :: Company
genCom = C [D "Research" laemmel [PU joost, PU marlow],
            D "Strategy" blair   []]
lammel, laemmel, joost, blair :: Employee
lammel  = E (P "Lammel" "Amsterdam") (S 8000)
laemmel = E (P "Laemmel" "Amsterdam") (S 8000)
joost   = E (P "Joost"   "Amsterdam") (S 1000)
marlow  = E (P "Marlow"  "Cambridge") (S 2000)
blair   = E (P "Blair"   "London")    (S 100000)
\end{code}
%endif

A well known benchmark for generic programming is the so-called
`Paradise' benchmark \cite{Lämmel03scrapyour}. It consists of set of
data types for a company structure, and a transformation on a value of
this type (increasing the salary).

\begin{code}
data Company  = C [Dept] deriving Show
data Dept     = D Name Manager [Unit] deriving Show
data Unit     = PU Employee | DU Dept deriving Show
data Employee = E Person Salary deriving Show
data Person   = P Name Address deriving Show
data Salary   = S Float deriving Show
type Manager  = Employee
type Name     = String
type Address  = String
\end{code}

This is a family of mutually recursive data types, since |Dept|
includes a list of |Unit|s, and |Unit| can contain a |Dept|. This
makes it seem like multirec is ideally suited to represent it.
However, it is not clear how to represent the lists in the |Company|
and |Dept| data types. One option is to specialize them for their
respective uses, and have two representations in the pattern functor.
We will use the original multirec representation, as detailed in
Section \ref{sec:multirec}.

\begin{code}
data CompanyU :: * -> * where
    Company   :: CompanyU Company
    DeptList  :: CompanyU [Dept]
    Dept      :: CompanyU Dept
    UnitList  :: CompanyU [Unit]
    Unit      :: CompanyU Unit
    Employee  :: CompanyU Employee
    Person    :: CompanyU Person
    Salary    :: CompanyU Salary

type instance PF CompanyU  = (I [Dept])                                :>: Company
                           :+: (K ())                                  :>: [Dept]
                           :+: (I Dept :*: I [Dept])                   :>: [Dept]
                           :+: (K String :*: I Employee :*: I [Unit])  :>: Dept
                           :+: (K ())                                  :>: [Unit]
                           :+: (I Unit :*: I [Unit])                   :>: [Unit]
                           :+: (I Employee)                            :>: Unit
                           :+: (I Dept)                                :>: Unit
                           :+: (I Person :*: I Salary)                 :>: Employee
                           :+: (K String :*: K String)                 :>: Person
                           :+: (K Float)                               :>: Salary
\end{code}

If we write the relevant instances of |Fam| and |El|, we can now use
|compos| to write a function to increase the salary:

\begin{code}
incS :: Float -> Company -> Company
incS f = incS' Company
  where
    incS' :: CompanyU ix -> ix -> ix
    incS' Salary  (S s)  = S $ (1 + f) * s
    incS' p       x      = compos incS' p x
\end{code}

However, we've duplicated the structure of the list in the
representation, and consequently we also have to duplicate the
respective cases in the conversion functions |from| and |to|. We would
like to define a separate structure with conversion functions for
lists, and then use that in the instance for the |Company| family.

If we extend multirec to represent data types of kind |* -> *|, as we
did for the simple functor representation in Section
\ref{sec:oneparam}, we can do this. We will not show the entire
implementation, but highlight the main points.

To represent lists, we create a second set of functors, used to
represent data types of kind |* -> *|. We will give them the same
names as the original functors, but prefix them with |F.|, as if they
were imported qualified. We can then add a composition functor to the
original set:

\begin{code}
data Comp f (phi :: * -> (* -> *) -> *) (xi :: * -> *) g (r :: * -> *) ix = 
  Comp { unComp :: (f F.I0 (g r ix) xi) }
\end{code}

It take four type arguments in addition to the |r| and |ix| that all
functors take. The first, |f|, is the functor representing a data type
of kind |* -> *|. The second |phi|, is the family it belongs, with
|xi| indicating its index within the family. Finally, |g| is the
functor representing a data type of kind |*| that is used at the
element positions of |f|.

Since our second set of functors can represent data types of kind |*
-> *|, we can define |gmap| over them. We do this in the familiar
manner: defining a type class |GMap| with a function |gmapF| for
mapping over the functors, and writing a top level wrapper |gmap| to
handle the conversion to and from actual data types. We will leave out
the implementation, which follows the same structure as |HFunctor|.

Using |gmap| and |gmapF|, we can define an |HFunctor| instance for
|Comp|. To do this, we use |gmap| and |gmapF| to map |hmap f| over the
outer functor, thus applying |f| to the inner functor.

\begin{code}
instance  (GMap phi' f, HFunctor phi g, GMap phi' (F.PF phi'), F.Fam phi', F.El phi' xi) => 
          HFunctor phi (Comp f phi' xi g) where
  hmap f p (Comp x) = Comp (
    F.gmapF
      (\pfrom pto (F.I0 x) -> F.I0 
          (F.gmap pfrom pto (hmap f p) x)
      )
      (F.proof :: phi' (g r ix) xi)
      (F.proof)
      (hmap f p)
      x
    )
\end{code}

The instance is not as straightforward as the description, but the
principle is the same. A small type signature is needed to fix the
type of |phi'|.

If we now define a generic representation for lists, we can use |Comp|
to use these lists in the representation of the company data type. We
can define a type synonym for composition with lists, and use it to
define the pattern functor for the family of company data types:

%% list rep at end of file.
\begin{code}
type ListOf = Comp (F.I []) ListU []

type instance PF CompanyU'  =    (ListOf (I Dept))        :>: Company
                            :+:  (    K String 
                                 :*:  I Employee 
                                 :*:  ListOf (I Unit)
                                 )                        :>: Dept
                            :+:  (I Employee)             :>: Unit
                            :+:  (I Dept)                 :>: Unit
                            :+:  (I Person :*: I Salary)  :>: Employee
                            :+:  (K String :*: K String)  :>: Person
                            :+:  (K Float)                :>: Salary
\end{code}

In the |Fam| instance, we now have to use both |F.I| and |I| in the
|Comp| cases. We will show one case, for |Company|:

%% real instance at end of file.
\begin{spec}
instance Fam CompanyU where
  from  Company (C ds)        = L  (Tag (compI ds))
  ldots
  to    Company (L (Tag ds))  = C  (unCompI ds)
  ldots
\end{spec}
\begin{code}
compI = Comp . F.I . F.I0 . map (I . I0)
unCompI = map (unI0 . unI) . F.unI0 . F.unI . unComp
\end{code}

If we try to apply this approach to the representation that allows
multiple type parameters, as shown in Section \ref{sec:multirecparams},
we have to ask the question: what do we mean by this composition.
Since these types can have multiple parameters, it is not clear at
which parameter we're applying the composition.

Taking the composition position as a type parameter is problematic:
what do we use at the other parameter positions? It seems our only
option is to specialize composition for types with only one type
parameter, by requiring that the element container is |E0|.

This would lead us to a data type like:

\begin{spec}
data Comp f (prf :: (* -> *) -> * -> * -> *) xi g (r :: * -> *) ix =
  Comp { unComp :: f (Case (Elems (g r ix)) (R0 prf (Elems (g r ix)))) xi }
\end{spec}

However, we run into a problem when defining the |HFunctor| instance
for this data type. There, we have to mention |Elems (g r ix)| in the
class context (in the type of a proof term), but neither |r| nor |ix|
are in scope. It is not clear how to solve this problem yet. It is not
possible to add these type variables to the type class parameters,
since they are universally quantified. We also cannot remove the |es|
type variable from proof terms, as this leads to problems with
non-matching element types elsewhere. Future research is needed to
solve this problem.

%% the boring stuff: list instance, real Fam instance for CompanyU'
%if style == newcode
\begin{code}
data ListU :: * -> (* -> *) -> * where
  List :: ListU a []

type instance F.PF ListU = (F.K () F.:+: F.E F.:*: F.I []) F.:>: []

instance F.Fam ListU where
  from List []     = F.Tag (F.L (F.K ()))
  from List (x:xs) = F.Tag (F.R (F.E x F.:*: F.I (F.I0 xs)))
  to   List (F.Tag (F.L (F.K ()))) = []
  to   List (F.Tag (F.R (F.E x F.:*: F.I (F.I0 xs)))) = x:xs

instance F.El ListU [] where
  proof = List

data CompanyU' :: * -> * where
    Company'  :: CompanyU' Company
    Dept'     :: CompanyU' Dept
    Unit'     :: CompanyU' Unit
    Employee' :: CompanyU' Employee
    Person'   :: CompanyU' Person
    Salary'   :: CompanyU' Salary

instance El CompanyU' Company where
  proof = Company'
instance El CompanyU' Dept where
  proof = Dept'
instance El CompanyU' Employee where
  proof = Employee'
instance El CompanyU' Unit where
  proof = Unit'
instance El CompanyU' Person where
  proof = Person'
instance El CompanyU' Salary where
  proof = Salary'

instance Fam CompanyU' where
  from Company' (C ds) = L (Tag (compI ds))
  from Dept' (D n m us) = R (L (Tag (K n :*: I (I0 m) :*: compI us)))
  from Unit' (PU e) = R (R (L (Tag (I (I0 e)))))
  from Unit' (DU d) = R (R (R (L (Tag (I (I0 d))))))
  from Employee' (E p s) = R (R (R (R (L (Tag (I (I0 p) :*: I (I0 s)))))))
  from Person' (P n a) = R (R (R (R (R (L (Tag (K n :*: K a)))))))
  from Salary' (S s) = R (R (R (R (R (R (Tag (K s)))))))
  to Company' (L (Tag ds)) = C (unCompI ds)
  to Dept' (R (L (Tag (K n :*: I (I0 m) :*: us)))) = D n m (unCompI us)
  to Unit' (R (R (L (Tag (I (I0 e)))))) = PU e
  to Unit' (R (R (R (L (Tag (I (I0 d))))))) = DU d
  to Employee' (R (R (R (R (L (Tag (I (I0 p) :*: I (I0 s)))))))) = E p s
  to Person' (R (R (R (R (R (L (Tag (K n :*: K a)))))))) = P n a
  to Salary' (R (R (R (R (R (R (Tag (K s)))))))) = S s
\end{code}
%endif
