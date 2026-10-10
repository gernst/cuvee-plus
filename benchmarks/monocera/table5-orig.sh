#!/bin/bash

LOG2YML=../output_tools/log2yml/log2yml

LOGDIR1="original_logs_from_paper/forall"
LOGDIR2="original_logs_from_paper/max"
LOGDIR3="original_logs_from_paper/min"
LOGDIR4="original_logs_from_paper/sum"


RESULT_FILE=table5-paper.tex

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
echo "Results for forall below\\" >> $RESULT_FILE
$YML2STATS -nocat -table5 $LOGDIR1 >> $RESULT_FILE
echo "Results for max below\\" >> $RESULT_FILE
$YML2STATS -nocat -table5 $LOGDIR2 >> $RESULT_FILE
echo "Results for min below\\" >> $RESULT_FILE
$YML2STATS -nocat -table5 $LOGDIR3 >> $RESULT_FILE
echo "Results for sum below\\" >> $RESULT_FILE
$YML2STATS -nocat -table5 $LOGDIR4 >> $RESULT_FILE

echo "\end{document}" >> $RESULT_FILE
echo "Done!"
