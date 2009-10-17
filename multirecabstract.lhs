\section{Abstract indices}
\label{sec:multirecabstract}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt
%options ghci -fglasgow-exts
%if style == newcode
\begin{code}
{-# OPTIONS_GHC -F -pgmF lhs2tex -optF --pre #-}
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

In section \ref{sec:multiparam} we used an indexed data type to
represent an arbitrary number of type parameters in the generic view
on a single data type.  We would like to apply this method to the
representation for mutually recursive data types used in Section
\ref{sec:multirec}. However, there is a problem. This problem shows up
in the type we expect |gmap| to have in this representation:

\begin{spec}
gmap ::  (Fam phi es, Fam phi es', GMap (PF phi)) =>
         (forall ix. es ix -> es' ix) -> phi es a -> phi es' b -> a -> b
\end{spec}

This function would convert the |a| to its functor representation
using the first proof, call a generic function which we'll call
|gmap'| to do the actual work, and then convert the result back to a
|b| using the second proof. The type signature of the function
|gmap'|, which works on the functor types, would be as follows:

\begin{spec}
class GMap phi f where
  gmap' :: (forall ix. es ix -> es' ix) -> (forall ix. r ix -> r' ix) -> f es r ix -> f es' r' ix
\end{spec}

This function takes two arguments: a function to transform the
elements, which was provided at the top level, and a function to
transform the recursive points. This function would be provided in
|gmap|, and would itself be |gmap| again, surrounded by wrapping and
unwrapping an |I0|.

A problem arises at the |I| instance. For example, if we represent a
list, a recursive position in the pattern functor has the type |I
[a]|. Now, when we map a function |a -> b| over it, \emph{the type
will change} and become |I [b]|. The same problem arises in the case
for |(:>:)|. In fact, this means that |gmap| doesn't even type check,
since the pattern functors for |a| and |b| are not the same, but
|gmap'| requires them to be. We can add an equality constraint |a ~
b|, but then we cannot change the element type any more.

A solution to this problem is to remove the concrete types from the
pattern functor. Both the |I| and |(:>:)| type should no longer expose
the original type, but should instead use abstract types to indicate
which type in the family they represent. The proof can then serve as a
relation between this abstract type, and a concrete type. For
example, it can map the type |Zero| to |Expr|, and |Suc Zero| to
|Decl|. An |I Zero| would then store an |Expr|, and an |f :>: (Suc
Zero)| would mark a part of the pattern functor as representing a
|Decl|.

We convert the code from Section \ref{sec:multirec} step by step. The
functor types don't need to change, and we use the same running
example of expressions with declarations and variables.
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

The first change is in the pattern functor. We declare natural number
types to serve as indices. Then we change all |Expr| indices to
|Zero|, all |Decl| indices to |Suc Zero| and all |Var| indices to |Suc
(Suc Zero)| in the |I| and |(:>:)| constructors.

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

We now change the GADT we used to prove membership of the family of
data types to also hold the relation between the concrete and the
abstract types. This changes its kind, and thus also the kind of |PF|,
which remains otherwise unchanged. Note that of the type arguments of |AST|,
the first is a member of the family (indicated with |kphi|) and the second is a
natural number type (indicated with |knat|). The pattern functor is now indexed
by natural numbers instead of types in the family.

\begin{code}
data AST :: kphi -> knat -> * where
  Expr  :: AST Expr  Zero
  Decl  :: AST Decl  (Suc Zero)
  Var   :: AST Var   (Suc (Suc Zero))

type family PF phi :: (knat -> *) -> knat -> *
type instance PF AST = PFAST
\end{code}

To store the values at the recursive position, multirec uses a simple
wrapper type |I0| that stored a value of index |ix| as-is. However, we
cannot do so anymore, as the index is now a natural number, which is
an empty type, and the concrete type is not visible in the pattern
functor. We solve this by existentially quantifying over the concrete
type, and storing the concrete recursive value together with a
relation between the concrete type and the abstract index. This means
that after unwrapping, we can use this relation (or proof) to convert
the value to a generic representation, and we can also pattern match
on it to recover the type information.

In the |Fam| type class, we change the pattern functor type to
indicate that we use this existential wrapper type at the recursive
positions. In the instance of |Fam|, we now have to provide the proof
at all the recursive positions.

\begin{code}
data R0 :: (kphi -> knat -> *) -> knat -> * where
  R0 :: phi a ix -> a -> R0 phi ix

class Fam phi where
  from  ::  phi a ix  -> a                   -> PF phi (R0 phi) ix
  to    ::  phi a ix  -> PF phi (R0 phi) ix  -> a

instance Fam AST where
  from  Expr  (Const i)    = L (Tag (L (K i)))
  from  Expr  (Add e1 e2)  = L (Tag (R (L (I (R0 Expr e1) :*: I (R0 Expr e2)))))
  from  Expr  (Mul e1 e2)  = L (Tag (R (R (L (I (R0 Expr e1) :*: I (R0 Expr e2))))))
  from  Expr  (EVar s)     = L (Tag (R (R (R (L (I (R0 Var s)))))))
  from  Expr  (Let d e)    = L (Tag (R (R (R (R (I (R0 Decl d) :*: I (R0 Expr e)))))))
  from  Decl  (s := e)     = R (L (Tag (L (I (R0 Var s) :*: I (R0 Expr e)))))
  from  Decl  (Seq d1 d2)  = R (L (Tag (R (I (R0 Decl d1) :*: I (R0 Decl d2)))))
  from  Var   s            = R (R (Tag (K s)))
  to    Expr  (L (Tag (L (K i))))                                          = Const i
  to    Expr  (L (Tag (R (L (I (R0 Expr e1) :*: I (R0 Expr e2))))))        = Add e1 e2
  to    Expr  (L (Tag (R (R (L (I (R0 Expr e1) :*: I (R0 Expr e2)))))))    = Mul e1 e2
  to    Expr  (L (Tag (R (R (R (L (I (R0 Var s))))))))                     = EVar s
  to    Expr  (L (Tag (R (R (R (R (I (R0 Decl d) :*: I (R0 Expr e))))))))  = Let d e
  to    Decl  (R (L (Tag (L (I (R0 Var s) :*: I (R0 Expr e))))))           = s := e
  to    Decl  (R (L (Tag (R (I (R0 Decl d1) :*: I (R0 Decl d2))))))        = Seq d1 d2
  to    Var   (R (R (Tag (K s))))                                          = s
\end{code}

We would like to keep using functions like |hmap| as we defined them
before, but the kind of the proof argument |phi| has changed: it now
takes an extra type |a|. The |a| isn't needed in generic functions
like |hmap|, so we choose to hide it using another existential type,
|Proof|. The |El| type class that produces proofs isn't changed, but
the instances now produce |Proof AST| terms for the abstract indices,
instead of |AST| terms for concrete indices.

\begin{code}
data Proof :: (kphi -> knat -> *) -> knat -> * where
  Proof :: phi a ix -> Proof phi ix

class El phi ix where
  proof :: phi ix

instance El (Proof AST)  Zero              where proof = Proof Expr
instance El (Proof AST)  (Suc Zero)        where proof = Proof Decl
instance El (Proof AST)  (Suc (Suc Zero))  where proof = Proof Var
\end{code}

% This code is the same as in the previous section, so it is not shown
% in the pdf.
%if style == newcode
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
%endif

With these changes, we can use the |HFunctor| class and the |hmap|
function exactly as defined in Section \ref{sec:multirec}. Functions
calling |hmap| have to be changed, however, because the recursive
positions are now wrapped in an |R0| instead of an |I0|. Since this
type is existentially quantified, we cannot write an unwrapping
function, and when pattern matching we have to add a type signature.
This type signature universally quantifies over some type variables,
but not over all, which means we need scoped type variables, by
turning on the ScopedTypeVariables extension to GHC.

\begin{code}
compos ::  forall phi a ix. (Fam phi, HFunctor (Proof phi) (PF phi)) =>
           (forall a ix. phi a ix -> a -> a) -> phi a ix -> a -> a
compos f p = to p . hmap rec . from p
  where
    rec :: forall ix. Proof phi ix -> R0 phi ix -> R0 phi ix
    rec _ (R0 p x) = R0 p (f p x)
\end{code}

Using |compos| still follows the same pattern. The only change is that
the proof is now a relation, but this only impacts the type signature
of |renameVar'|, not the code.

\begin{code}
renameVar :: Expr -> Expr
renameVar = renameVar' Expr
  where
    renameVar' :: AST a ix -> a -> a
    renameVar' Var  s  = s ++ "_"
    renameVar' p    x  = compos renameVar' p x
\end{code}

We have changed the functors used in our generic representation to
expose only abstract indices, and not concrete types. By doing this,
we have made sure that the type of the pattern functor doesn't change
when we change the type of the parameters of the original type. This
change involved changing the proof of family membership to a relation
between a concrete type and an abstract index. The indexing on the
functors now uses the abstract indices. At the recursive positions, we
still store the concrete type. This type is existentially quantified,
so it is not visible on the outside. To recover this type later, it is
paired with a relation to its abstract index. With this change in
place, we can now add support for type parameters to multirec, using
the technique from Section \ref{sec:multiparam}.
