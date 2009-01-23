\section{Arbitrary number of type parameters}
%include polycode.fmt
%format family = "\mathbf{family}"
%format :+: = "\oplus"
%format :*: = "\otimes"
%if style == newcode
\begin{code}
{-# LANGUAGE TypeFamilies
           , TypeOperators
		   , GADTs
		   , KindSignatures
		   , EmptyDataDecls
           #-}
\end{code}
%endif

What we want to do, is abstract over the number of type parameters a
type former takes. This means also abstracting over the kind of the
recursive positions. The idea is, to use numbers on the type level to
indicate the number of type parameters, and to indicate which type
parameter an element corresponds to.

In a dependently typed programming language, we can apply this idea
directly. [TODO: How do I insert Agda code in here?]

In Haskell, we can represent this as follows: we hide the type of the
parameter in the |E| constructor, using existential quantification. We
define a GADT that allows us to recover this type by pattern matching,
and we parametrize all functors by this GADT. The functors now become:

\begin{code}
data K a        (es :: * -> * -> *) r = K a
data E a        (es :: * -> * -> *) r where
    E :: (es a e) -> e -> E a es r
data I          (es :: * -> * -> *) r = I r
data (f :*: g)  (es :: * -> * -> *) r = f es r :*: g es r
data (f :+: g)  (es :: * -> * -> *) r = L (f es r) | R (g es r)
\end{code}
%if style == newcode
\begin{code}
infixr 7 :*:
infixr 6 :+:
\end{code}
%endif

Notice that the type |e| of the parameter in the |E| constructor is
not visible in its type, |E a es r|. However, it is visible in the
type of the GADT that is stored with it. This allows recovery of the
type by pattern matching. The type |a| in the type of |E| is the type
level number, used to indicate which type parameter it is. This is
needed to ensure that we don't change the order of the parameters.
[TODO: clear up, example].

As an example of the GADT that is stored with the parameters, let's
consider representing a data type with two type parameters. The GADT
will be as follows:

\begin{code}
data Zero
data Suc a

data ParamS2 :: * -> * -> * -> * -> *  where
    Param1 :: ParamS2 a b Zero        a
    Param2 :: ParamS2 a b (Suc Zero)  b
\end{code}

In essence, this is a type level function, taking |Zero| to type |a|,
and |Suc Zero| to type |b|. In the type of the functors, |a| and |b|
have been instantiated to concrete types by partially applying
|ParamS2|, since it needs to have kind |* -> * -> *| there.

As a concrete example, consider a tree data type that stores one type
of value in its leaves, and another in the branches:

\begin{code}
data Tree a b = Leaf a | Branch (Tree a b) b (Tree a b)
\end{code}

We define a type family, and make an instance for |Tree|:

\begin{code}
type family PF a :: (* -> * -> *) -> * -> *

type instance (PF (Tree a b)) = E Zero :+: I :*: E (Suc Zero) :*: I
\end{code}

In the `from' function, we bundle up one of the constructors of the
|ParamS2| type with the actual parameter value. In the `to' function,
we pattern match on the GADT, which allows us to return the correct
type again.

\begin{code}
fromTree  :: Tree a b -> PF (Tree a b) (ParamS2 a b) (Tree a b)
fromTree (Leaf a)        = L (E Param1 a)
fromTree (Branch l b r)  = R (I l :*: E Param2 b :*: I r)
toTree    :: PF (Tree a b) (ParamS2 a b) (Tree a b) -> Tree a b
toTree (L (E Param1 a))                  = Leaf a
toTree (R (I l :*: E Param2 b :*: I r))  = Branch l b r
\end{code}
