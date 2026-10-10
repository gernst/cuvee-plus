#!/bin/bash

LOG2YML=../output_tools/log2yml/log2yml

LOGDIR1="original_logs_from_paper/forall"
LOGDIR2="original_logs_from_paper/max"
LOGDIR3="original_logs_from_paper/min"
LOGDIR4="original_logs_from_paper/sum"

RESULT_FILE=table3-paper.txt

echo "Generating output file $RESULT_FILE"

YML2STATS=../output_tools/yml2stats/yml2stats

echo "Results for forall below" > $RESULT_FILE
$YML2STATS -nocat $LOGDIR1 >> $RESULT_FILE
echo "Results for max below" >> $RESULT_FILE
$YML2STATS -nocat $LOGDIR2 >> $RESULT_FILE
echo "Results for min below" >> $RESULT_FILE
$YML2STATS -nocat $LOGDIR3 >> $RESULT_FILE
echo "Results for sum below" >> $RESULT_FILE
$YML2STATS -nocat $LOGDIR4 >> $RESULT_FILE

cat $RESULT_FILE

echo "Done!"
