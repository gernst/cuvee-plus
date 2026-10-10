#!/bin/bash

LOG2YML=../output_tools/log2yml/log2yml

LOGDIR="run-test-result"

RESULT_FILE=table5.tex

echo '
\documentclass[a4paper,landscape]{article}
\usepackage{longtable}
\usepackage{booktabs}
\usepackage{xcolor}
\usepackage{hyperref}
\newcommand{\cpachecker}{\textsc{CPA}}
\newcommand{\monocera}{\textsc{Mono}}
\newcommand{\seahorn}{\textsc{Sea}}
\newcommand{\tricera}{\textsc{Tri}}
\setcounter{table}{4}
\begin{document}
' > $RESULT_FILE

echo "Generating output file $RESULT_FILE"

YML2STATS=../output_tools/yml2stats/yml2stats
$YML2STATS -table5 $LOGDIR >> $RESULT_FILE

echo "\end{document}" >> $RESULT_FILE
echo "Done!"
