\section{Multirec: mutually recursive data types}
\label{sec:multirec}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt
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
           #-}
\end{code}
%endif

The functor representation used in section \ref{sec:functorrep} and
beyond can only represent \emph{regular data types}. In particular, it
cannot represent a family of mutually recursive data types. This is
unfortunate, as these occur frequently in practice.

The approach used in the multirec library \cite{multirec} still uses a
functor representation, but it can represent families of mutually
recursive data types.  It does this by \emph{indexing} the recursive
points with a type that indicates to which type in the family the
recursion goes.

Consider the following functor types:

\begin{code}
data K a             (r :: kphi -> *) (ix :: kphi) = K a
data I (xi :: kphi)  (r :: kphi -> *) (ix :: kphi) = I (r xi)
data (f :+: g)       (r :: kphi -> *) (ix :: kphi) = L (f r ix) | R (g r ix)
data (f :*: g)       (r :: kphi -> *) (ix :: kphi) = f r ix :*: g r ix

infixr 6 :+:
infixr 8 :*:
\end{code}

The |K|, |(:+:)| and |(:*:)| functors now take an indexed recursive
type, and are indexed themselves, but are otherwise unchanged. The
interesting change is in the |I| type. It takes an extra type
parameter |xi|, which indicates which type to recurse on. Note that it
differs from the functor index |ix|, which indicates which type we are
currently describing.

We have used kinds |kphi| instead of |*| to indicate that only a restricted
subset of types is allowed. Only types from the family of data types we are
describing are used to index the functors.

So far, the index |ix| of the functor components is completely free:
there is nothing constraining it. For this, we introduce a new
building block: |(:>:)|. This constructor tags a functor with an
index, indicating that this part of the functor describes the indicated
type in the family.

\begin{code}
data (f :>: (xi :: kphi))  (r :: kphi -> *) (ix :: kphi) where
  Tag :: f r ix -> (f :>: ix) r ix
\end{code}

As an example, let us consider a data type of expressions, also used in
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

These data types are mutually recursive: |Expr| can contain a |Decl|,
and |Decl| can contain an |Expr|. Both contain |Var|s. To represent
this data type, we can use the following pattern functor:

\begin{code}
type PFAST  =    (    K Int
                 :+:  I Expr  :*: I Expr
                 :+:  I Expr  :*: I Expr
                 :+:  I Var
                 :+:  I Decl  :*: I Expr
                 ) :>: Expr
            :+:  (    I Var   :*: I Expr
                 :+:  I Decl  :*: I Decl
                 ) :>: Decl
            :+:       K String :>: Var
\end{code}

When writing a conversion function to |PFAST|, we need to define a function
that takes either an |Expr|, a |Decl| or a |Var|, but no other types. Similar
to section \ref{sec:multiparam}, we want to restrict the kind. This time we
require an enumeration kind, containing the three types in our family. To this
end, we define a GADT that functions as a proof that a type is in our family of
AST types:

\begin{code}
data AST :: kphi -> * where
  Expr  :: AST Expr
  Decl  :: AST Decl
  Var   :: AST Var
\end{code}

We can use this data type when referring to the entire family. When we
do, we'll refer to it as |phi|. Using this data type, we can define a
type family for the pattern functor as we did earlier. This time,
however, it gives the pattern functor for a family of types instead of
a single type.

\begin{code}
type family PF phi :: (kphi -> *) -> kphi -> *
type instance PF AST = PFAST
\end{code}

We choose a shallow embedding as before, which means we don't convert
recursive values, but store them as is. We need a simple wrapper type
for this, which we'll call |I0|. We also define an unwrapping
function, |unI0|. Using the wrapper, we can define the type class for
families that can be represented generically. It is parametrized by
the family (e.g. the |AST| type defined earlier). It contains the
familiar conversion functions |from| and |to|. Each takes a value of
|phi|, which restricts the type |ix| to one of the types in the
family.

\begin{code}
data I0 a = I0 { unI0 :: a }

class Fam phi where
  from  ::  phi ix  -> ix            -> PF phi I0 ix
  to    ::  phi ix  -> PF phi I0 ix  -> ix
\end{code}

We can now give an instance of this type class for the types in the
family |AST|. By pattern matching on the values of |AST|, we refine
the type |ix| to one of |Expr|, |Decl| or |Var|, which allows us to
pattern match on it. The combination of an indexed pattern functor and
the tagging functor makes sure we choose the right part of the functor
for each type. For example, if we were to start with |R L| instead of
|L| when converting an |Expr|, we'd get a type error. The pattern
functor when choosing the right sum followed by a left sum is tagged
with |Decl|.  However, in the type signature of |from|, the pattern
functor has index |ix|, which pattern matching on the |AST| value
determined to be |Expr|.

\begin{code}
instance Fam AST where
  from  Expr  (Const i)    = L (Tag (L (K i)))
  from  Expr  (Add e1 e2)  = L (Tag (R (L (I (I0 e1) :*: I (I0 e2)))))
  from  Expr  (Mul e1 e2)  = L (Tag (R (R (L (I (I0 e1) :*: I (I0 e2))))))
  from  Expr  (EVar s)     = L (Tag (R (R (R (L (I (I0 s)))))))
  from  Expr  (Let d e)    = L (Tag (R (R (R (R (I (I0 d) :*: I (I0 e)))))))
  from  Decl  (s := e)     = R (L (Tag (L (I (I0 s) :*: I (I0 e)))))
  from  Decl  (Seq d1 d2)  = R (L (Tag (R (I (I0 d1) :*: I (I0 d2)))))
  from  Var   s            = R (R (Tag (K s)))
  to    Expr  (L (Tag (L (K i))))                                = Const i
  to    Expr  (L (Tag (R (L (I (I0 e1) :*: I (I0 e2))))))        = Add e1 e2
  to    Expr  (L (Tag (R (R (L (I (I0 e1) :*: I (I0 e2)))))))    = Mul e1 e2
  to    Expr  (L (Tag (R (R (R (L (I (I0 s))))))))               = EVar s
  to    Expr  (L (Tag (R (R (R (R (I (I0 d) :*: I (I0 e))))))))  = Let d e
  to    Decl  (R (L (Tag (L (I (I0 s) :*: I (I0 e))))))          = s := e
  to    Decl  (R (L (Tag (R (I (I0 d1) :*: I (I0 d2))))))        = Seq d1 d2
  to    Var   (R (R (Tag (K s))))                                = s
\end{code}

We can define a higher-order map function on the functors used here.
This function transforms the indexed recursive positions. It is
similar to the normal |fmap| on functors, but lifted to indexed
functors.

\begin{code}
class HFunctor phi f where
  hmap :: (forall ix. phi ix -> r ix -> r' ix) -> f r ix -> f r' ix
\end{code}

Note that the function argument passed to |hmap| uses a rank-2 type.
Since we wish to restrict |ix| to only those types in the family
|phi|, we add an explicit proof argument. However, we also need to
obtain this proof somehow when we call this function. Rather than
passing it along, we define a type class to generate proofs.

\begin{code}
class El phi ix where
  proof :: phi ix
\end{code}

An instance of this type class is a statement that the index |ix|
exists in the family |phi|, with |proof| as the witness. We give the
instances for |AST| as follows:

\begin{code}
instance El AST Expr  where proof = Expr
instance El AST Decl  where proof = Decl
instance El AST Var   where proof = Var
\end{code}

Now we can define instances of hmap for all the higher order functors.
In the |I| case, we call the function argument, using the proof that
|xi| is an element of |phi|. The other instances are straightforward,
and very similar to functor instances in the non-indexed case.

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

We can use |hmap| to define other generic function. One example is |compos|
\cite{DBLP:conf/icfp/BringertR06}. This function applies a transformation
function to the children of a value. It is non-recursive, so the user has to
call the function recursively himself. It works on the concrete types, not on
the generic representation. By pattern matching on the proof terms, type
information can be recovered.

As an example of its use, the following function renames all variables in an
expression by adding an underscore to their name:

\begin{code}
renameVar :: Expr -> Expr
renameVar = renameVar' Expr
  where
    renameVar' :: AST ix -> ix -> ix
    renameVar' Var  s  = s ++ "_"
    renameVar' p    x  = compos renameVar' p x
\end{code}

The definition of |compos| is fairly straightforward. It converts the
type to a generic representation, uses |hmap| to apply the provided
function to all recursive positions, unwrapping the |I0| before
applying and wrapping afterward. Finally it converts back from the
generic representation.

\begin{code}
compos :: (Fam phi, HFunctor phi (PF phi)) => (forall ix. phi ix -> ix -> ix) -> phi ix -> ix -> ix
compos f p = to p . hmap (\p -> I0 . f p . unI0) . from p
\end{code}

The multirec paper \cite{multirec} and the corresponding library
contain further examples, including a |fold| function with convenient
algebras. The library also supports Template Haskell
\cite{Sheard02templatemeta-programming} generation of the pattern
functor and the |from| and |to| functions.

Using the multirec approach, we can generically represent families of
mutually recursive data types, and access the recursive points in a
type safe way using indexed data types. However, the approach suffers
from the same limitations as the simple functor representation of
Section \ref{sec:functorrep}: it is unable to represent parametrized
data types in a way that allows us to generically access the elements.
In the next sections, we will adapt multirec with our extension from
Section \ref{sec:multiparam} to lift this limitation.
