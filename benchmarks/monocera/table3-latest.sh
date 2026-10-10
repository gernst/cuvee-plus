#!/bin/bash

LOG2YML=../output_tools/log2yml/log2yml

LOGDIR="run-test-result"

RESULT_FILE=table3.txt

echo "Converting .log files to .yml files, this can take a few minutes."
for name in `find "$LOGDIR" -name "*.log1"`; do
echo
    $LOG2YML $name
done

echo "Generating output file $RESULT_FILE"

YML2STATS=../output_tools/yml2stats/yml2stats
$YML2STATS -latest $LOGDIR > $RESULT_FILE

cat $RESULT_FILE

echo "Done!"
