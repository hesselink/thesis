\section{Multirec with type parameters}
%include polycode.fmt
%include forall.fmt
%format family = "\mathbf{family}"
%if style /= newcode
%format :+: = "\oplus"
%format :*: = "\otimes"
%format <?> = "\varobar"
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

We could add elements to the representation of mutually recursive
datatypes along the same lines as we did in section
\ref{sec:multiparam}. However, this means adding an extra type
parameter to the functors. We can prevent this by exploiting the
similarity between the indexed recursive position, and the indexed
elements.

We can combine two non-indexed types into a type that can hold either
type; this type is fittingly called |Either|. We can do something
similar for indexed types. We will call this type |Case|, and just
like |Either| has two constructors |Left| and |Right|, |Case| has
constructors |CL| and |CR|.

\begin{code}
data Left ix
data Right ix

data Case :: (* -> *) -> (* -> *) -> (* -> *) where
  CL  :: l  ix -> Case l r (Left   ix)
  CR  :: r  ix -> Case l r (Right  ix)
\end{code}

|Case| itself is indexed, but not with the index |ix| of the type it
contains, but with index |Left ix| or |Right ix|, depending on which
constructor is used. This way, the type contains more information
about which value is contained within. This grants us more type
safety, and prevents us from having to define `impossible' cases for
functions.

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
\end{code}
%endif

We will adapt the running example slightly. Instead of storing |Int|s
as constants in our expression language, we will parametrize |Expr|
and |Decl| with the type of the constants:

\begin{code}
data Expr a  =  Const a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  EVar Var
             |  Let (Decl a) (Expr a)

data Decl a  =  Var := (Expr a)
             |  Seq (Decl a) (Decl a)

type Var     =  String

data Zero
data Suc a
\end{code}

We will use the |Case| type to store both the elements and the
recursive values in the |I| functor. This means that we will have |I|
values indexed with |Left ix| for element |ix|, and with |Right ix|
for recursion to type |ix|. To make this clearer, we introduce two
type synonyms |Elem| and |Rec| for |Left| and |Right|. We then adapt
the type of the pattern functor. Notice how in the first alternative
for |Expr|, we now have an |I (Elem Zero)| instead of a |K Int|,
indicating that the constants in our expression language are now
polymorphic, and their type is indicated by the first type parameter,
instead of being fixed to |Int|

\begin{code}
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

type family PF phi :: (* -> *) -> * -> *
type instance PF AST = PFAST
\end{code}

We need an indexed type to hold elements. However, since we only have
one element type, we will use a simple wrapper type |E0| which ignores
the index, instead of the more flexible but also more complex type
from section \ref{sec:multiparam}.

We parametrize the family index |AST| by the element collection. By
partially applying this type later, we can fix the element type,
making sure we don't combine an |Expr a| with a |Decl b|. When
representing families with multiple type parameters, this also allows
us to indicate with type is used in which position of which type.

\begin{code}
data E0 a ix = E0 { unE0 :: a }

data AST :: (* -> *) -> * -> * -> * where
  Expr  :: AST (E0 a) (Expr a)  Zero
  Decl  :: AST (E0 a) (Decl a)  (Suc Zero)
  Var   :: AST (E0 a) Var       (Suc (Suc Zero))
\end{code}

We extend |R0| with an extra type parameter to hold the element types.
We then define the |Fam| type class again, using |Case| at the
recusive position to allow both elements, and recursive values. In the
instance for |AST|, we use the case constructors |CL| for elements,
and |CR| for recursive values.

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

% This code is the same as in the previous section, so it is not shown
% in the pdf.
%if style == newcode
\begin{code}
data Proof :: (* -> * -> *) -> * -> * where
  Proof :: phi a ix -> Proof phi ix

class El phi ix where
  proof :: phi ix

data NatPrf :: * -> * where
  PZ :: NatPrf Zero
  PS :: NatPrf n -> NatPrf (Suc n)

instance El NatPrf Zero where
  proof = PZ

instance El NatPrf a => El NatPrf (Suc a) where
  proof = PS proof
\end{code}
%endif

We make no change to the |El| type class (which indicated that an
index is a member of a type) or the |Proof| wrapper. In the |El|
instances for |AST|, we partially apply it to |E0 a| so that it has
the right kind.

Since our recursive positions now hold a choice of two indexed types,
we also need to pass along a choice of two proofs: for elements, we
use the natural number proof |NatPrf| as shown in section
\ref{sec:multiparam}, and for the recursive positions, we use the family
proof. To combine these two proofs, we can use the |Case| type, just
as we do for the values themselves.

To use these proofs, we define two instances of |El| for |Case|, which
prove that if |ix| is part of the types |pl| or |pr|, then |Left ix|
or |Right ix| are part of the type |Case pl pr|. We also define a type
synonym for the type of proofs for families of recursive types with
elements.

\begin{code}
instance El (Proof (AST (E0 a)))  Zero              where proof = Proof Expr
instance El (Proof (AST (E0 a)))  (Suc Zero)        where proof = Proof Decl
instance El (Proof (AST (E0 a)))  (Suc (Suc Zero))  where proof = Proof Var

instance El pl ix => El (Case pl pr) (Left ix) where
  proof = CL proof

instance El pr ix => El (Case pl pr) (Right ix) where
  proof = CR proof

type FamPrf phi (es :: * -> *) = Case NatPrf (Proof (phi es))
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

The code for |HFunctor| and |hmap| again stays unchanged. However,
when we call |hmap| in |compos|, we now have to pass a function that
transforms a |Case| into another |Case|. Rather than doing ad-hoc
pattern matching on case, we define a mapping function over |Case|.
Given two functions that transform the left and right components of
the case given a proof, this function can transform the entire |Case|,
given a |Case| of proofs to match.

Note that since the type indicates that the indices for the proof and
the value are the same, we only need to (and indeed, only can) give
the cases where both are either a |CL| or a |CR|.
\begin{code}
(<?>) :: (forall ix. pl  ix -> f  ix -> f'  ix) ->
         (forall ix. pr  ix -> g  ix -> g'  ix) ->
         Case pl pr ix -> Case f g ix -> Case f' g' ix
(f <?> g) (CL p) (CL x) = CL (f p x)
(f <?> g) (CR p) (CR y) = CR (g p y)
\end{code}

We can now define |compos| again. We use |<?>| to pass two functions,
|el| and |rec|, to |hmap|, one for the elements, and the other for the
recursive values. We have to give both these functions a type
signature, as it is no longer possible to infer these correctly in the
presence of higher-rank polymorphism. The |el| function does nothing,
while the |rec| function is the same as before.

\begin{code}
compos ::  forall phi es a ix. (Fam phi es, HFunctor (FamPrf phi es) (PF phi)) => 
           (forall a ix. phi es a ix -> a -> a) -> phi es a ix -> a -> a
compos f p = to p . hmap (el <?> rec) . from p
  where
    el  :: forall ix. NatPrf ix -> es ix -> es ix
    el  = const id
    rec :: forall ix. Proof (phi es) ix -> R0 phi es ix -> R0 phi es ix
    rec _ (R0 p x) = R0 p (f p x)
\end{code}

As an example, we use compos to add one to all the constants in a
term. We do this by requiring a |Num| constraint on the element type,
and then pattern matching on the |Const| constructor of the |Expr|
type.

\begin{code}
addOne :: Num a => Expr a -> Expr a
addOne = addOne' Expr
  where
    addOne' :: Num a => AST (E0 a) b ix -> b -> b
    addOne' Expr (Const i)  = Const (i + 1)
    addOne' p    x          = compos addOne' p x
\end{code}

While it is fine to use |compos| to do this, |gmap| would be more
suited for the task. With everything in place now, we can finally
define it. It takes a function transforming the elements |es| into
elements |es'|. The family of types |phi| should be an instance of
|Fam| for both sets of elements. Finally, we require an |HFunctor|
instance for the pattern functor of the family, using a proof that the
elements indices are natural numbers, and the recursive values are
members of the family.

The top level function takes two family proofs, one to convert the |a|
to a generic representation, and one to convert the result back to a
|b|. In the call to |hmap|, we again map two functions over the
|Case|. For the elements, we just apply the function that transforms
the elements. At the recursive positions, we unwrap both the proof and
the value, and apply |gmap| recursively.

Notice that we use |es'| in the proof at the |HFunctor| constraint.
This provides us with a proof of |phi es' b ix| instead of |phi es a
ix| in |rec|, which it needs for the call to |gmap| and to wrap the
resulting value in an |R0| again.

\begin{code}
gmap ::  forall phi es es' a b ix. (Fam phi es, Fam phi es', HFunctor (FamPrf phi es') (PF phi)) =>
         (forall ix. es ix -> es' ix) -> phi es a ix -> phi es' b ix -> a -> b
gmap f pfrom pto = to pto . hmap (el <?> rec) . from pfrom
  where
    el :: forall ix. NatPrf ix -> es ix -> es' ix
    el = const f
    rec :: forall ix. Proof (phi es') ix -> R0 phi es ix -> R0 phi es' ix
    rec (Proof pto) (R0 pfrom x) = R0 pto (gmap f pfrom pto x)
\end{code}

We can now write the addOne function using |gmap|. To transform the
elements, we unwrap the |E0|, add one, and wrap again. We pass in Expr
twice, once to indicate the input type, and once to indicate the
output type.

\begin{code}
addOne2 :: Num a => Expr a -> Expr a
addOne2 = gmap (E0 . (+1) . unE0) Expr Expr
\end{code}

One thing we cannot do with |compos| is change the type of the
elements in an expression, since the transformation function has type
|a -> a|. Using |gmap| this is no problem. For example, the following
function takes an expression of doubles, and rounds all constants to
produce an expression of integers.

\begin{code}
roundExpr :: Expr Double -> Expr Integer
roundExpr = gmap (E0 . round . unE0) Expr Expr
\end{code}
