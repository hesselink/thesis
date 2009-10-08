\documentclass[11pt, twoside, a4paper, openright]{report}
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
\usepackage{fancyhdr}
\bibpunct{[}{]}{,}{n}{,}{,}

\fancyhf{}
\fancyhead[LO]{\textsc{\rightmark}}
\fancyhead[RE]{\textsc{\leftmark}}
\fancyhead[LE,RO]{\thepage}

\pagestyle{fancy}

\setlength{\parindent}{0pt}
\setlength{\parskip}{\baselineskip}
\setlength{\headheight}{14pt}


\begin{document}
\title{Generic programming with fixed points for parametrized datatypes}
\author{Erik Hesselink}

\maketitle
\setcounter{tocdepth}{1}
\tableofcontents

\input{introduction}
\input{typeparameters}
\input{benchmark}
\input{conclusion}
\bibliographystyle{plain}
\bibliography{thesis}

\end{document}
