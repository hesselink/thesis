\chapter{Introduction}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt

Most programs consist of two components: structured data, and
functionality on this data. In functional programming languages like
Haskell, these two things are separate. Data is defined by of
algebraic data types (ADTs), consisting of one or more constructors
with zero or more fields.  Functions work on these data types,
transforming values into values of a possibly different type.

Some functions are specific for a particular data type. For example,
if we have a function to increase the salary on an employee data type,
it makes no sense to apply it to a data type representing an
arithmetic expression. However, many functions, like equality, or
binary serialization, can be defined for many data types. Moreover,
their definition often follows a fixed pattern, making it boring and
error-prone. Lastly, if the definition of the data type is adapted,
all these functions have to be adapted as well.

The aim of generic programming is to solve these problems. We define
generic or type indexed functions, which have different behavior
depending on the type of the value passed to it. This allows us to
write a function only once, and reuse it on different data types, or
on different versions of the same data type.

Generic programs often work by induction on the shape of the type
argument. This shape is described by a so-called pattern functor,
consisting of constants for fields with a constant type, sums for
choice between constructors, products for combining multiple fields
and the identity functor for recursive positions. The original type is
isomorphic to the fixed point of the pattern functor. Generic
functions can be used on the original data type by defining conversion
functions from the original type to the pattern functor and vice
versa.

The first language to use such a fixed point view on data types was
PolyP \cite{polyp}, an extension to a Haskell-like language. Other
views on data types have also been used. The sum-of-products view also
represents types as sums and products, but without information about
the recursive positions. Generic Haskell
\cite{Hinze00polytypicvalues}, a preprocessor for Haskell, uses this
view, although it has later been extended with generic views
\cite{Holdermans06genericviews}, allowing the use of different
representations. The Haskell libraries Lightweight Implementation of
Generics and Dynamics (LIDG) \cite{Cheney02alightweight} and
Extensible and Modular Generics for the Masses (EMGM)
\cite{Hinze04genericsfor, emgm} also use the sum-of-products view.
Another view is the spine view, which makes constructors and their
application explicit. It is used in Scrap Your Boilerplate
\cite{Lämmel03scrapyour, Lämmel04scrapmore, Lämmel05scrapyour,
Hinze06reloaded, Hinze06revolutions}.

The fixed point view is limited in the sense that it is restricted to
representing regular data types. Among other things, this means that
it is not possible to represent families of mutually recursive data
types. The multirec library \cite{multirec} uses indexed functors to
allow type safe access to the recursive positions of a family of
mutually recursive data types, viewed as fixed points. This allows the
use of generic functions like fold on these families of data types
(see also Section \ref{sec:multirec}).

Another limitation of the fixed point view is the representation of
type parameters. PolyP used functors of kind |* -> *|, allowing
meaningful access to one type parameter. Multirec does not have any
meaningful representation of type parameters. Libraries like LIGD and
EMGM offer several representations, based on the number of type
parameters. This means that parts of your generic programming library
have to be implemented multiple times, once for each representation.
In this thesis, we will develop an extension of the fixed point view
that allows us to represent an arbitrary number of type parameters in
a meaningful way.

In chapter \ref{cha:typeparameters}, we will develop this extension.
We will do this gradually, starting with a simple fixed point view. We
will first add support for a single type parameter, and then extend
this to multiple parameters. After that, we will integrate this
approach into multirec, allowing the representation of parametrized
families of mutually recursive data types.

In chapter \ref{cha:benchmark}, we will introduce a comparison of
generic programming libraries in Haskell by Rodriguez et al.
\cite{benchmark}, and discuss how our extensions have improved the
score of multirec. We will conclude in chapter \ref{cha:conclusion}
with related work and directions for future research.
