\documentclass[11pt, twoside, dvipdfm, a4paper, openright]{report}
\usepackage{pxfonts}
%include polycode.fmt
% if also including lagda, use the following instead, and rename to .lagda:
%\def\textmu{}
%%include agda.fmt
% special commands for correct spacing of "* where" in GADTs.
\newcommand\plainwhere{\mathbf{where}}
\newcommand\spacewhere{\;\plainwhere}
\let\where\plainwhere
\usepackage[a4paper]{geometry}
\usepackage{natbib}
\usepackage{hyperref}
\usepackage[pdftex]{graphicx}
\bibpunct{[}{]}{,}{n}{,}{,}

\setlength{\parindent}{0pt}
\setlength{\parskip}{\baselineskip}

\begin{document}
\title{Generic programming with fixed points for mutually recursive datatypes}
\author{Erik Hesselink}

\maketitle
\tableofcontents

\input{introduction}
\input{benchmark}
\input{typeparameters}
\input{applications}
\bibliographystyle{plain}
\bibliography{thesis}

\end{document}
