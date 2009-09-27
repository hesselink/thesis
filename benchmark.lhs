\chapter{Benchmarking multirec}
\label{cha:benchmark}
%include polycode.fmt
%include forall.fmt
%include thesis.fmt

For the past years, research on generic programming in Haskell has
been a hot topic, and as a result, the number of libraries for
generics programming in Haskell has exploded. On the one hand, this
is a good thing: it allows us to compare and evaluate different
approaches to generic programming. On the other hand, this makes it
hard to choose a library for generic programming, especially since it
is difficult to compare the different libraries.

Alexey Rodriguez et al. \cite{benchmark} have developed a benchmark
for generic programming libraries that aims to alleviate this problem.
It selects a range of types of problems that generic programming can
solve, and scores a range of libraries on their ability to solve these
problems. Additionally, some other quality aspects like ease of use
are also judged. Using the results of this benchmark, it is possible
to select an appropriate generic programming library for a certain
application.

Although the technical report does not include a benchmark for the
multirec \cite{multirec} library, this is included in Alexey
Rodriguez' thesis \cite{thesis_alexey}. The results of this benchmark
are reproduced in figure \Todo{add figure and ref}.

\Todo{check if universe size is increased}

The original multirec library could only represent types of kind |*|
in a way that gave access to the elements of a data type generically.
This meant that it was impossible to define the functions |gmap| and
|crushRight|. In the benchmark, multirec was rated `bad' when evaluating
it on abstraction over type constructors.

With the extensions defined in this thesis, we believe this rating can
now be changed to `good'. Defining |gmap| and |crushRight| is no
different from defining other generic functions in multirec, and they
can be used to define |mapBinTree| and |flattenWTree| as required.

The benchmark also judges libraries on ease of use. The multirec
library did not score very well on this because of the large number of
compiler extensions used. The additions in this thesis do not require
any additional extensions to be used. However, writing a generic
function now requires the use of scoped type variables for the
function 'tying the knot', making this slightly more complex.

The complexity for the actual representation of the elements varies.
If elements are not present, the extra complexity is minimal. One
element data types can use the |E0| container, which is a regular ADT.
For representations of (families of) data types with multiple
elements, complexity is higher, as this requires the use of the
indexed element container type |(:||:)|. Additionally, an additional
type class is needed to mirror an existing type class for indexed
elements.  For example, when defining the |gleft| function
(Section \ref{sec:producers}), we need both a |Small| type class to generate
normal values, and a |SmallEl| type class to generate indexed values.

Since the ease of use of the multirec library was already low, and the
added complexity of our extension scales with the number of type
parameters you need to support, we feel we have not increased the
complexity of the library substantially.

\Todo{automatic generation of instances?}
