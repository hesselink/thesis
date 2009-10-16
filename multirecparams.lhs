\section{Multirec with type parameters}
\label{sec:multirecparams}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt
%options ghci -fglasgow-exts -pgmL lhs2tex -optL --pre
%if style == newcode
\begin{spec}
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
\end{spec}
%endif

We could add elements to the representation of mutually recursive
data types along the same lines as we did in Section
\ref{sec:multiparam}. However, this means adding an extra type
parameter to the functors. We can prevent this by exploiting the
similarity between the indexed recursive position, and the indexed
elements.

We can combine two non-indexed types into a type that can hold either
type; this type is fittingly called |Either|. We can do something
similar for indexed types. We will call this type |Case|, and just
like |Either| has two constructors |Left| and |Right|, |Case| has
constructors |CL| and |CR|.

\begin{spec}
data Left ix
data Right ix

data Case :: (kl -> *) -> (kr -> *) -> (keitherlr -> *) where
  CL  :: l  ix -> Case l r (Left   ix)
  CR  :: r  ix -> Case l r (Right  ix)
\end{spec}

|Case| itself is indexed, but not with the index |ix| of the type it contains,
but with index |Left ix| or |Right ix|, depending on which constructor is used.
As indicated, if the left and right types are indexed by types of kind |kl| and
|kr| respectively, then |Case l r| is indexed by a type of kind |keitherlr|.
This way, the type contains more information about which value is contained
within. This grants us more type safety, and prevents us from having to define
`impossible' cases for functions.

% This code is the same as in the previous section, so it is not shown
% in the pdf.
%if style == newcode
\begin{spec}
data K a        (r :: * -> *) ix = K a
data I xi       (r :: * -> *) ix = I (r xi)
data (f :+: g)  (r :: * -> *) ix = L (f r ix) | R (g r ix)
data (f :*: g)  (r :: * -> *) ix = f r ix :*: g r ix

infixr 6 :+:
infixr 8 :*:

data (f :>: xi)  (r :: * -> *) ix where
  Tag :: f r ix -> (f :>: ix) r ix
\end{spec}
%endif

We will adapt the running example slightly. Instead of storing |Int|s
as constants in our expression language, we will parametrize |Expr|
and |Decl| with the type of the constants:

\begin{spec}
data Expr a  =  Const a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  EVar Var
             |  Let (Decl a) (Expr a)
\end{spec}
%if style == newcode
\begin{spec}
             deriving Show
\end{spec}
%endif

\begin{spec}
data Decl a  =  Var := (Expr a)
             |  Seq (Decl a) (Decl a)
\end{spec}
%if style == newcode
\begin{spec}
             deriving Show
\end{spec}
%endif

\begin{spec}

type Var     =  String

data Zero
data Suc a
\end{spec}

We will use the |Case| type to store both the elements and the
recursive values in the |I| functor. This means that we will have |I|
values indexed with |Left ix| for element |ix|, and with |Right ix|
for recursion on type |ix|. To make this clearer, we introduce two
type synonyms |Elem| for |Left| and |Rec| for |Right|. We then adapt
the type of the pattern functor. Notice how in the first alternative
for |Expr|, we now have an |I (Elem Zero)| instead of a |K Int|,
indicating that the constants in our expression language are now
polymorphic, and their type is indicated by the first type parameter,
instead of being fixed to |Int|

\begin{spec}
type Elem  = Left
type Rec   = Right

type PFAST  =    (    I (Elem Zero)
                 :+:  I (Rec Zero)        :*: I (Rec Zero)
                 :+:  I (Rec Zero)        :*: I (Rec Zero)
                 :+:  I (Rec (Suc (Suc Zero)))
                 :+:  I (Rec (Suc Zero))  :*: I (Rec Zero)
                 ) :>: Rec Zero
            :+:  (    I (Rec (Suc (Suc Zero)))  :*: I (Rec Zero)
                 :+:  I (Rec (Suc Zero))        :*: I (Rec (Suc Zero))
                 ) :>: Rec (Suc Zero)
            :+:       K String :>: Rec (Suc (Suc Zero))

type family PF phi :: (knat -> *) -> knat -> *
type instance PF AST = PFAST
\end{spec}

We need an indexed type to hold elements. However, since we only have
one element type in this example, we will use a simple wrapper type
|E0| which ignores the index, instead of the more flexible but also
more complex type from Section \ref{sec:multiparam}. If it was needed,
we could use the more complex type instead.

We parametrize the family index |AST| by the element collection. By
partially applying this type later, we can fix the element type,
making sure we don't combine an |Expr a| with a |Decl b|. When
representing families with multiple type parameters, this also allows
us to indicate which parameter position is corresponds to which
element type in each family type.

\begin{spec}
data E0 a ix = E0 { unE0 :: a }

data AST :: (knat -> *) -> kphi -> knat -> * where
  Expr  :: AST (E0 a) (Expr a)  Zero
  Decl  :: AST (E0 a) (Decl a)  (Suc Zero)
  Var   :: AST (E0 a) Var       (Suc (Suc Zero))
\end{spec}

We extend |R0| with an extra type parameter to hold the element types.
We then define the |Fam| type class again, using |Case| at the
recursive position to allow both elements, and recursive values. In the
instance for |AST|, we use the case constructors |CL| for elements,
and |CR| for recursive values.

%% De types in from en to staan niet netjes onder elkaar omdat dat
%% niet past.

\begin{spec}
data R0 :: ((knat -> *) -> * -> knat -> *) -> (knat -> *) -> knat -> * where
  R0 :: phi es a ix -> a -> R0 phi es ix

class Fam phi es where
  from  ::  phi es a ix  -> a -> PF phi (Case es (R0 phi es)) (Rec ix)
  to    ::  phi es a ix  -> PF phi (Case es (R0 phi es)) (Rec ix) -> a

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
\end{spec}

% This code is the same as in the previous section, so it is not shown
% in the pdf.
%if style == newcode
\begin{spec}
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
\end{spec}
%endif

We make no change to the |El| type class (which indicates that an
index is a member of a type) or the |Proof| wrapper. In the |El|
instances for |AST|, we partially apply |AST| to |E0 a| so that it has
the right kind.

Since our recursive positions now hold a choice of two indexed types,
we also need to pass along a choice of two proofs: for elements, we
use the natural number proof |NatPrf| as shown in Section
\ref{sec:multiparam}, and for the recursive positions, we use the family
proof. To combine these two proofs, we can use the |Case| type, just
as we do for the values themselves.

To use these proofs, we define two instances of |El| for |Case|, which
prove that if |ix| is part of the types |pl| or |pr|, then |Left ix|
or |Right ix| are part of the type |Case pl pr|. We also define a type
synonym for the type of proofs for families of recursive types with
elements.

\begin{spec}
instance El (Proof (AST (E0 a)))  Zero              where proof = Proof Expr
instance El (Proof (AST (E0 a)))  (Suc Zero)        where proof = Proof Decl
instance El (Proof (AST (E0 a)))  (Suc (Suc Zero))  where proof = Proof Var

instance El pl ix => El (Case pl pr) (Left ix) where
  proof = CL proof

instance El pr ix => El (Case pl pr) (Right ix) where
  proof = CR proof

type FamPrf phi (es :: knat -> *) = Case NatPrf (Proof (phi es))
\end{spec}

% This code is the same as in the previous section, so it is not shown
% in the pdf.
%if style == newcode
\begin{spec}
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
\end{spec}
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
\begin{spec}
(<?>) ::  (forall ix. pl  ix -> f  ix -> f'  ix) ->
          (forall ix. pr  ix -> g  ix -> g'  ix) ->
          Case pl pr ix -> Case f g ix -> Case f' g' ix
(f <?> g) (CL p) (CL x) = CL (f p x)
(f <?> g) (CR p) (CR y) = CR (g p y)
\end{spec}

We can now define |compos| again. We use |<?>| to pass two functions,
|el| and |rec|, to |hmap|, one for the elements, and the other for the
recursive values. We have to give both these functions a type
signature, as it is no longer possible to infer these correctly in the
presence of higher-rank polymorphism. The |el| function does nothing,
while the |rec| function is the same as before.

\begin{spec}
compos ::  forall phi es a ix. (Fam phi es, HFunctor (FamPrf phi es) (PF phi)) =>
           (forall a ix. phi es a ix -> a -> a) -> phi es a ix -> a -> a
compos f p = to p . hmap (el <?> rec) . from p
  where
    el  :: forall ix. NatPrf ix -> es ix -> es ix
    el  = const id
    rec :: forall ix. Proof (phi es) ix -> R0 phi es ix -> R0 phi es ix
    rec _ (R0 p x) = R0 p (f p x)
\end{spec}

As an example, we use compos to add one to all the constants in a
term. We do this by requiring a |Num| constraint on the element type,
and then pattern matching on the |Const| constructor of the |Expr|
type.

\begin{spec}
addOne :: Num a => Expr a -> Expr a
addOne = addOne' Expr
  where
    addOne' :: Num a => AST (E0 a) b ix -> b -> b
    addOne' Expr (Const i)  = Const (i + 1)
    addOne' p    x          = compos addOne' p x
\end{spec}

While it is fine to use |compos| to do this, |gmap| would be more
suited for the task. With everything in place now, we can finally
define it. It takes a function transforming the elements |es| into
elements |es'|. The family of types |phi| should be an instance of
|Fam| for both sets of elements. Finally, we require an |HFunctor|
instance for the pattern functor of the family, using a proof that the
elements indices are natural numbers, and the recursive values are
members of the family.

The top level function takes two family proofs, one to convert the
input value |a| to a generic representation, and one to convert the
result back to a |b|. In the call to |hmap|, we again map two
functions over the |Case|. For the elements, we just apply the
function that transforms the elements. At the recursive positions, we
unwrap both the proof and the value, and apply |gmap| recursively.

Notice that we use |es'| in the proof at the |HFunctor| constraint.
This provides us with a proof of |phi es' b ix| instead of |phi es a
ix| in |rec|, which it needs for the call to |gmap| and to wrap the
resulting value in an |R0| again.

\begin{spec}
gmap ::  forall phi es es' a b ix. (Fam phi es, Fam phi es', HFunctor (FamPrf phi es') (PF phi)) =>
         (forall ix. es ix -> es' ix) -> phi es a ix -> phi es' b ix -> a -> b
gmap f pfrom pto = to pto . hmap (el <?> rec) . from pfrom
  where
    el :: forall ix. NatPrf ix -> es ix -> es' ix
    el = const f
    rec :: forall ix. Proof (phi es') ix -> R0 phi es ix -> R0 phi es' ix
    rec (Proof pto) (R0 pfrom x) = R0 pto (gmap f pfrom pto x)
\end{spec}

We can now write the |addOne| function using |gmap|. To transform the
elements, we unwrap the |E0|, add one, and wrap again. We pass in
|Expr| twice, once to indicate the input type, and once to indicate
the output type.

\begin{spec}
addOne2 :: Num a => Expr a -> Expr a
addOne2 = gmap (E0 . (+1) . unE0) Expr Expr
\end{spec}

One thing we cannot do with |compos| is change the type of the
elements in an expression, since the transformation function has type
|a -> a|. Using |gmap| this is no problem. For example, the following
function takes an expression of doubles, and rounds all constants to
produce an expression of integers.

\begin{spec}
roundExpr :: Expr Double -> Expr Integer
roundExpr = gmap (E0 . round . unE0) Expr Expr
\end{spec}

We have shown how to integrate the extension to the fixed point view
on data types we developed in Section \ref{sec:multiparam} into the
multirec approach (Section \ref{sec:multirec}). Rather than add an
extra argument to the functors, we have exploited the similarity
between the indexed element container in our extension and the indexed
recursive positions in multirec. We use |Case|, which is similar to an
indexed |Either|, to store both in the |I| functor. With this
extension, we can define |gmap| for families of mutually recursive
data types.

\subsection{Deep embedding}

So far, we have used a shallow embedding: at the recursive positions,
we store the original data type, instead of its generic representation.
For some applications, it can be more convenient to work with a deep
embedding, where the entire data type is converted to a generic
representation.

For example, when defining a \emph{type indexed data type}, you extend
a data type in a generic way. This can be used to add meta-variables to
a data type to use during term rewriting, to annotate a data type with
position information during parsing, etc. When you extend the generic
representation of a type in this way, you want the recursive positions
to contain the extended type, not the original type. The deep
embedding is therefor a natural fit for this kind of application.

When we have functors of kind |* -> *| as in Section
\ref{sec:functorrep}, we use the well-known |Fix| data type (also
called |Mu|):

\begin{spec}
data Fix f = In { out : f (Fix f) }
\end{spec}

A type |Fix f| contains an |f|, with |Fix f| at the recursive
positions, producing a deep embedding. For indexed functors, as we
used in Section \ref{sec:multirec} and after, a similar fixpoint
data type is also possible. This data type is itself indexed, but is
otherwise similar to |Fix| above. We will call it |HFix|, and define
it as:

\begin{spec}
data HFix (f :: (kphi -> *) -> kphi -> *) ix = HIn { hout :: f (HFix f) ix }
\end{spec}

This data type can be used to create a deep embedding using the indexed
functors without elements. When we introduce elements, however, we
want to have a choice at the |I| position: either we store an element
(the left case) or we recurse. This means we want to produce a type
which looks as follows:

\begin{spec}
type DeepF phi es ix = PF phi (Case es (PF phi (Case es ...))) ix
\end{spec}

When we have a function application |f (g x)|, we can use function
composition to write this as |(f . g) x|. We can also do this at the
type level, using \emph{functor composition} to flatten the nested
type applications at the recursive positions above:

\begin{spec}
data (f :.: g) (r :: * -> *) ix = Comp { unComp :: (f (g r) ix) }
\end{spec}

We can now rewrite the type |DeepF| above as:

\begin{spec}
type DeepF phi es ix = (PF phi :.: Case es) ((PF phi :.: Case es) ...) ix
\end{spec}

This type can be represented in Haskell by using the |HFix| type above:

\begin{spec}
type DeepF phi es ix = HFix (PF phi :.: Case es) ix
\end{spec}

We can now convert types to the deep embedding. We can either use the
|Fam| type class and recursively apply the |from| function, or define
a new type class |FamFix|. We will do the latter here, but we do not
give instances, which are straightforward: they are the same as
before, with an extra |Fix| around the functors and a call to |hfrom|
instead of the |R0| constructor.

\begin{spec}
class FamFix phi es where
  hfrom  ::  phi es a ix  -> a                             -> HFix (PF phi :.: Case es) ix
  hto    ::  phi es a ix  -> HFix (PF phi :.: Case es) ix  -> a
\end{spec}

To write functions that operate on this fixpoint representation, the
type classes like |HFunctor| don't have to change: they make no
assumptions about the recursive positions. Only the top-level
function, which `ties the knot' using knowledge about the recursive
position, has to change. As an example, we write |gmap| in this
representation. It consists of a function |gmapFix|, which converts to
and from the generic representation, and calls a function |gmapFixF|.
This function does the actual work, unwrapping the |HFix| and |Comp|,
applying the function |f| to the elements, and calling itself at the
recursive positions, and finally wrapping in |Comp| and |HFix| again.

\begin{spec}
gmapFix ::  forall phi es es' a b ix.
            (FamFix phi es, FamFix phi es', HFunctor (FamPrf phi es) (PF phi)) =>
            (forall ix. es ix -> es' ix) -> phi es a ix -> phi es' b ix -> a -> b
gmapFix f pfrom pto = hto pto . gmapFixF f (Proof pfrom) . hfrom pfrom

gmapFixF ::  forall phi es es' a b ix. (HFunctor (FamPrf phi es) (PF phi)) =>
             (forall ix. es ix -> es' ix) -> Proof (phi es) ix ->
             HFix (PF phi :.: Case es) ix -> HFix (PF phi :.: Case es') ix
gmapFixF f _ = HIn . Comp . hmap (el <?> rec) . unComp . hout
  where
    el :: forall ix. NatPrf ix -> es ix -> es' ix
    el = const f
    rec ::  forall ix. Proof (phi es) ix ->
            HFix (PF phi :.: Case es) ix -> HFix (PF phi :.: Case es') ix
    rec = gmapFixF f
\end{spec}

We have shown how to use a generic representation that uses a deep
embedding, where the recursive positions of a data type are also
converted to the generic representation. This involved using a
combination of the indexed fixpoint data type |HFix|, and indexed
functor composition |(:.:)|

To use this embedding, none of the type classes defining our generic
functions have to change. Only the top level function, which `ties the
knot', has to be adapted. The deep embedding is slightly more
complicated because it needs two functions here, one converting to and
from the generic representation, and the other working only on this
generic representation. On the other hand, it avoids using
existentials, and needs proof terms only to fix the types of the
family and the elements, and not for conversion. 

Performance measurements on generic rewriting \cite{genericrewriting}
show that the deep embedding is slower than the shallow embedding, due
to unneeded conversions to and from the generic representation.
However, optimization techniques like fusion (using GHC's rewrite
rules) might improve this situation. In the end, the choice between
shallow and deep embedding depends on which representation is more
natural for each application.

\subsection{Producers}
\label{sec:producers}

As in Section \ref{sec:multiparam:producers}, we will show a
\emph{producer} function (in the shallow embedding), which produces a
generic value from only non-generic inputs. We will again implement
the generic `left' and `right' values of a data type.

We begin with a type class for defining our function |hzero| on the
functors. It takes an argument function which can generate the
recursive positions, and produces a functor~|f|. Both the argument
function and |hzero| itself take a proof and a boolean argument. The
proof restricts the index being generated, and the boolean indicates
whether to create an |L| or an |R| constructor in the sum case.

\begin{spec}
class HZero prf f where
  hzero :: (forall ix. prf ix -> Bool -> r ix) -> prf ix -> Bool -> f r ix
\end{spec}

This function shows the need to tag with |Rec n| instead of just |n|.
If we were to tag the functors at top level with indices without a
|Rec|, the recursive positions would still take a |Case| of two
proofs, and so have indices |Left| and |Right|. This means we would
need to parametrize the |HZero| type class over \emph{two} proofs, and
instantiate the first proof to |FamPrf phi es| and the second to
|Proof (phi es)|. By tagging with |Rec n|, we avoid this and can
parametrize over a single proof type.

The instances for |I|, |K|, |:+:| and |:*:| are similar to those in
Section \ref{sec:multiparam:producers}. In the |I| case, we apply the
function for recursive positions, using the |El| type class to
generate a proof. For |K|, we use the |Small| type class again to
generate concrete values. In case of a sum, we use the boolean
argument to choose either |L| or |R|, and for a product we generate
both sides and combine them.

\begin{spec}
instance El prf xi => HZero prf (I xi) where
  hzero f _ left = I (f proof left)

instance Small x => HZero prf (K x) where
  hzero _ _ _ = K small

instance (HZero prf f, HZero prf g) => HZero prf (f :+: g) where
  hzero f p True   = L  (hzero f p True  )
  hzero f p False  = R  (hzero f p False )

instance (HZero prf f, HZero prf g) => HZero prf (f :*: g) where
  hzero f p left = hzero f p left :*: hzero f p left
\end{spec}

The instance for |:>:| is more interesting. Remember that this data
type is a GADT, with one constructor, |Tag|, which constrains its
first type argument (which we will call |xi| here) and its index |ix|
to be the same type.

The code we wish to write is simple: we want to call |hzero|
recursively, and wrap the result in |Tag|. However, which proof do we
pass? If we pass the proof we get as an argument to |hzero|, we get a
value at index |ix|, but |Tag| needs a value at index |xi|. If we
construct a proof at index |xi| using the |proof| function, we
generate a value at index |xi| which |Tag| accepts, but which is the
wrong type to return, since we need to return a value at index |ix|.

The solution is to check if the types |xi| and |ix| are the same, and
if they are, show this to the type checker. Note that they do not
\emph{have} to be the same here. When constructing a value of |:>:|,
|xi| and |ix| are the same, but the instance of |HZero| can be called
with different types for each (for example, by using an explicit type
signature on the result of a call to |hzero|).

Since we cannot pattern match on types, we cannot compare all types,
but only indices of the same type constructor. As a result, we do not
just return a |Bool|. Instead, if the types match, we produce an
\emph{equality proof} |t1 :=: t2| \cite{dynamictyping}. We can pattern
match on this proof to introduce an equality constraint in the type
checker between these two types.

The equality type is defined as follows. It takes two type arguments,
but the only constructor constrains these types to be the same.

\begin{spec}
data (:=:) :: * -> * -> * where
  Refl :: a :=: a

infix 4 :=:
\end{spec}

The type class for testing type equality will be called |EqS|. It
takes two proofs at different indices, and compares the indices for
equality. It returns either |Nothing| when the types don't match, or
|Just Refl| when they do. Note that we can only define the function
|eqS| if the proof is itself a GADT. If it is a regular parametrized
type, we cannot learn anything about the type by pattern matching on
the values, and so we are never allowed to produce an equality proof
between the two different types.

As an example, we give the |EqS| instance for |AST|, the family of
expressions and declarations. The |AST| type is applied to the
elements container and wrapped in a |Proof| type, as this is how it is
used in the generic functions.

We also give instances for |NatPrf| and |Case prf1 prf2|. In these
instances, we need the congruence property of equality: if we know
that |a :=: b|, then we also know that |f a :=: f b|. We can prove
this using the function |eqCong|.

\begin{spec}
class EqS prf where
  eqS :: prf ix -> prf ix' -> Maybe (ix :=: ix')

instance EqS (Proof (AST (E0 a))) where
  eqS (Proof Expr)  (Proof Expr)  = Just Refl
  eqS (Proof Decl)  (Proof Decl)  = Just Refl
  eqS (Proof Var )  (Proof Var )  = Just Refl
  eqS _     _     = Nothing

eqCong :: a :=: b -> f a :=: f b
eqCong Refl = Refl

instance EqS NatPrf where
  eqS PZ       PZ       = Just Refl
  eqS (PS p1)  (PS p2)  = fmap eqCong (eqS p1 p2)
  eqS _        _        = Nothing

instance (EqS prf1, EqS prf2) => EqS (Case prf1 prf2) where
  eqS (CL p1)  (CL p2)  = fmap eqCong (eqS p1 p2)
  eqS (CR p1)  (CR p2)  = fmap eqCong (eqS p1 p2)
  eqS _        _        = Nothing
\end{spec}

We can now bring all this together to give the instance for |:>:|. We
require an instance |El prf xi| so we can produce a proof |prf xi|. We
get a proof |prf ix| as an argument, and we compare the two index
types for equality. If they match, we can pattern match on |Refl|,
introducing an equality constraint |xi ~ ix|, and we are allowed to
return the value we want.

The case where the indices don't match (|Nothing|) cannot occur with a
well-typed |Fam| instance, but only with a manual call to |hzero|
specifying a type signature. Therefor, instead of changing the
signature of |hzero| to deal with errors by using |Maybe| or |Either|,
we use the |error| function.

\begin{spec}
instance (HZero prf f, El prf xi, EqS prf) => HZero prf (f :>: xi) where
  hzero f p left = let p' = proof :: prf xi in
    case eqS p p' of
      Just Refl -> Tag (hzero f p' left)
      Nothing   -> error
        "Indices ix and xi do not match in HZero instance for :>:."
\end{spec}

Before we can define the top level function |gleft|, we need to be
able to generate values of |Case f g ix|, given functions to create |f
ix| and |g ix|, because we use |Case| at the recursive positions. The
function is fairly straightforward: we take a |Case| of two proof
arguments and pattern match on it. If it is a |CL|, we produce a |CL|
with an |f| inside, and similarly for |CR| and |g|.

\begin{spec}
hzeroC ::  (forall ix. prf  ix -> Bool -> f ix) ->
           (forall ix. prf' ix -> Bool -> g ix) ->
           Case prf prf' ix -> Bool -> Case f g ix
hzeroC f g (CL p)  left = CL  (f  p left)
hzeroC f g (CR p)  left = CR  (g  p left)
\end{spec}

Now we can tie all this together in the top level function |gleft|,
which generates left-biased values for any type in a family |phi|. The
function calls |hzero| to generate a generic value, and then converts
it to a concrete value using |to|. The function to construct the
recursive points generates a case with |hzeroC|. The left branch
generates elements, using the previously defined type class |SmallEl|.
The right branch generates recursive values by calling |gleft|. As
before, type signatures are required because of pattern matching on
existential values, and to constrain the type of |phi| to match
between the top-level definition and the local definitions.

\begin{spec}
gleft ::  forall phi es a ix. (Fam phi es, HZero (FamPrf phi es) (PF phi), SmallEl NatPrf es) =>
          phi es a ix -> a
gleft p = to p $ hzero gcase (CR (Proof p)) True
  where
    gcase :: forall ix. FamPrf phi es ix -> Bool -> Case es (R0 phi es) ix
    gcase = hzeroC (const . smallEl) rec
    rec :: forall ix. Proof (phi es) ix -> Bool -> R0 phi es ix
    rec (Proof p) left = R0 p (gleft p)
\end{spec}

We have shown how to define a generic producer function |gleft| for
families of mutually recursive data types, which produces a
left-biased value of a data type. The use of a GADT which restricts
the index of our functors in the generic representation required
equality testing on types. We have shown how to do so using the |EqS|
type class. We have also shown how to prove this equality to the type
checker using the |(:=:)| type. We even needed the congruence property
of equality, bringing Haskell programming closer to the realm of proof
assistants and dependently typed programming languages.

%if style == newcode
\begin{spec}
class SmallEl prf es where
  smallEl :: prf ix -> es ix

class Small x where
  small :: x

instance Small () where small = ()
instance Small Int where small = 0
instance Small Integer where small = 0
instance Small Char where small = '\0'
instance Small [a] where small = []

instance Small a => SmallEl NatPrf (E0 a) where
  smallEl _ = E0 small
\end{spec}
%endif

\subsection{Fold}

In multirec, it is possible to define a fold function that is very
similar in its use to a hand-written fold on a data type. It takes an
algebra that contains a tuple with an algebra for each data type. Each
of these contains another tuple, with a function for each constructor.
These functions take an argument for each value in the constructor,
and produces a result. The fold also takes a value, and applies the
algebra to obtain a final result.

The type of the algebra depends on the data type. We use a type family
to encode this. It takes the functor representing the data type, the
recursive result type, and the index in the family. Note that the
result type is also indexed, since we may want to generate a different
result type for each type in the family.

\begin{spec}
type family Alg  (f :: (* -> *) -> * -> *) (r :: * -> *) (ix :: *) :: *
\end{spec}

The type family instances describe how the components of the algebra
depend on the structure of the data type. We will not show all
instances, but show the instance for |I| as an example. At a recursive
position, we get a recursive result, and convert it to a result at the
current index.

\begin{spec}
type instance Alg (I xi) r ix = r xi -> r ix
\end{spec}

We now define a type class to apply these algebras to a functor.

\begin{spec}
class Fold (f :: (* -> *) -> * -> *) where
  alg :: Alg f r ix -> f r ix -> r ix
\end{spec}

The instances are straightforward: the algebra can just be applied
directly in most cases, and in others we call |alg| recursively.
Again, we only show the case for |I|.

\begin{spec}
instance Fold (I xi) where
  alg f (I x) = f x
\end{spec}

We can now write a top level function that applies an algebra to a
value. It does this by first converting to the generic representation,
mapping the fold on all recursive positions, and the applying the
algebra on the top level functor.

\begin{spec}
fold ::  forall phi ix r . (Fam phi, HFunctor phi (PF phi), Fold (PF phi)) =>
         Algebra phi r -> phi ix -> ix -> r ix
fold f p =  alg (f p) .
            hmap (\ p (I0 x) -> fold f p x) .
            from p
\end{spec}

To adapt this fold to support the extension of multirec with elements,
we add a type for these elements to the |Alg| type family. This type
can be instantiated to a list of types (|(:||:)|), a simple container
for one element type, or an empty type in case the family has no type
parameters.

\begin{spec}
type family Alg  (f :: (* -> *) -> * -> *) (l :: * -> *) (r :: * -> *) (ix :: *) :: *
\end{spec}

We split the type family instance for |I| into two parts, on for a
|Right| index, which indicates recursive positions, and one for a
|Left| index, indicating elements. In the |Right| case, we produce the
same function type as before: from a value at the recursive index to a
value at the current index.

\begin{spec}
type instance Alg (I (Right xi)) l r ix = r xi -> r ix
\end{spec}

At the element position, we want a function from the element type at
the index |xi| to a result at index |ix|. However, what is the element
type at a given index? Since the type |l| is abstract here, we cannot
make any assumptions about it. Instead, we define a type family |ElTy|
which takes a container type and an index, and produces the element
type at that index.

\begin{spec}
type family ElTy (es :: * -> *) (ix :: *) :: *

type instance ElTy (a :|: b) Zero     = a
type instance ElTy (a :|: b) (Suc n)  = ElTy b n
\end{spec}

The instances for |(:||:)| are straightforward. At index |Zero|, we
return the type of the head of the list. At index |Suc n|, we call
|ElTy| recursively on the tail, with index |n|.

We can now give the instance for |Alg| for the |I| functor at a |Left|
index:

\begin{spec}
type instance Alg (I (Left  xi)) l r ix = ElTy l xi -> r ix
\end{spec}

The type class |Fold| which applies the algebra to a functor has to be
changed slightly. The functor we apply the algebra to now has a |Case
l r| at the |I| positions, representing the choice between an element
and a recursive result. The functor itself is indexed with |Right|,
indicating that it represents a type in the family, not an element. We
add the element container type |l| as a class parameter, so we can add
a constraint on it later.

\begin{spec}
class Fold l (f :: (* -> *) -> * -> *) where
  alg :: Alg f l r ix -> f (Case l r) (Right ix) -> r ix
\end{spec}

In the instance for |I|, we again distinguish between a |Right| and a
|Left| index. The case for a |Right| index is similar to the original
case: we can just apply the algebra directly, apart from the fact that
we have to unwrap the |Case| constructor.

\begin{spec}
instance Fold l (I (Right xi)) where
  alg f (I (CR x)) = f x
\end{spec}

The instance for a |Left| index is more interesting. Our functor
contains an |l|, the element container, at index |xi|. However, our
algebra is a function that takes an |ElTy l xi|. To convert from the
first to the second, we create a type class, |ElemContainer|,
containing a function |get| which does just this.

We give an instance for |(:||:)|, which returns the contents of a |Z|
constructor, and unwraps an |S| and calls |get| recursively. Since we
require an |ElemContainer b| constraint on this instance, we also have
to give a case for |Nil|. As before, we call |magic| to indicate that
this case will never be reached since |Nil| is an empty type.

\begin{spec}
class ElemContainer (es :: * -> *) where
    get :: es ix -> ElTy es ix

instance ElemContainer Nil where
  get = magic

instance ElemContainer b => ElemContainer (a :|: b) where
  get (Z  x) = x
  get (S  x) = get x
\end{spec}

On the |Fold| instance for |I| at a |Left| index, we now require an
|ElemContainer l| constraint. We can then call |get| to retrieve a
value of type |ElTy l xi| from the element container |l|.

\begin{spec}
instance ElemContainer l => Fold l (I (Left xi)) where
  alg f (I (CL x)) = f (get x)
\end{spec}

The |fold| function itself doesn't change conceptually. We change
|hmap| to |rmap|, which maps only over the right part of a |Case|. We
also have to explicitly type the function we map over the recursive
positions, as we did before.

\begin{spec}
fold ::  forall phi es a ix r . (Fam phi es, HFunctor (FamPrf phi es) (PF phi), Fold es (PF phi)) =>
         Algebra phi es r -> phi es a ix -> a -> r ix
fold f p =  alg (f p) .
            rmap rec (CR (Proof p)) .
            from p
  where
    rec :: forall ix a b. Proof (phi es) ix -> R0 phi es ix -> r ix
    rec _ (R0 p x) = fold f p x
\end{spec}

We can now write very natural algebras. For example, if we represent
the trees from Section \ref{sec:multiparam}, we can write an algebra
over them like this:

\begin{spec}
treeAlg :: Algebra TreeU (Int :|: String :|: Nil) Int
treeAlg _  =  (\e -> e)
           &  (\n e o -> n + length e + o)
\end{spec}

The first part of the algebra applies to |Leaf| constructors, which
contain the first element, which is an |Int|. We just return it, since
the return type of our algebra is also |Int|. The second case applies
to the |Branch| constructor, which contains a recursive result from
the left tree, a |String|, and a recursive result from the right tree.
We take the length of the string, and add the result to the two
recursive results. Note that |&| is just a synonym for |(,)| which
allows us to use less parentheses.

Given an example tree:

\begin{spec}
example :: Tree Int String
example = Branch (Branch (Leaf 3) "def" (Leaf 2)) "abc" (Leaf 1)
\end{spec}

We can now apply the algebra to the example by calling |fold treeAlg
Tree example|, to obtain the result |12|.
