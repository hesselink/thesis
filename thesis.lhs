\documentclass[11pt, twoside, dvipdfm, a4paper, openright]{report}
%include polycode.fmt
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
