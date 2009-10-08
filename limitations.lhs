\chapter{Limitations}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt
%format ? = "~\ldots"

The extension described in Section \ref{sec:multiparam} can represent data types with any number of parameters. The limitation is that all parameters have to be of kind |*|. It is not possible to represent, for example, a generalized rose tree:

\begin{code}
data GRose f a = GRose a (f (GRose f a))
\end{code}

The type argument |a| is not a problem, as it has kind |*|. The
argument |f|, however, has kind |* -> *|, and it is not clear how to
represent this. The only option is to use |K| to represent the |f|.
This works for some applications, like equality, but not for others,
like folding.

The extension in Section \ref{sec:multirecparams} has another
limitation. It models elements of a type family, not explicit type
abstraction. This means that a type constructor can not be applied to
two different types within one family. As an example, consider the
following family of two data types.

\begin{code}
data T a b  = One (B a) | Two (B b)
data B a    = B a
\end{code}

We can see that |B| is applied to type |a| in the constructor |One|,
and to the type |b| in the constructor |Two|. If we try to represent
this family, we can see the problem. We parametrize the \emph{family}
with two types, and have to choose one which is contained in a |B|.
There is no way to indicate that it can be either one, depending on
the |A| constructor chosen.

\begin{spec}
data TU (* -> *) -> * -> * -> * where
  T :: TU (a :|: b :|: Nil) (T a b) Zero
  B :: TU (a :|: b :|: Nil) (B ?) (Suc Zero)

type instance TU  = (I (Rec (Suc Zero)) :+: I (Rec (Suc Zero)))  :>: Zero
                  :+: (I (Elem ?))                               :>: (Suc Zero)
\end{spec}

To solve this problem, one would have to model type application and
abstraction. Then, we could indicate in the two |I| occurrences
representing the two constructors of |A| to which type argument |B| is
applied. It is not clear yet how to model type abstraction in this
way.
