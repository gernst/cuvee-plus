#!/bin/bash

FILEPATH=/host
TESTS_FOLDER=polished_tests


# Edit below two lines to change what to test
# Available provers: monocera tricera seahorn cpachecker
# Available ops: forall sum min max
prover=$1
op=$2
TWALL=$3
TCPU=$4
filepathlist=$5
no_malloc=$6

mkdir -p $FILEPATH/run-test-result/${prover}/${op}
cd $FILEPATH/run-test-result/${prover}
#find $FILEPATH/polished_tests${no_malloc}/${prover}/${op}/*.c -type f | sort | xargs  realpath  > $FILEPATH/run-test-result/${prover}/${op}/${op}${no_malloc}_list
#echo $filelist
#cat <<< "$filelist"  > $FILEPATH/run-test-result/${prover}/${op}/${op}${no_malloc}_list
#filelist=$(find $FILEPATH/${TESTS_FOLDER}${nomalloc}/${prover}/${op}/*.c -type f | xargs  realpath)
#cat <<< "$filelist" > "$FILEPATH/run-test-result/${prover}/${op}/${op}${no_malloc}_list"

#$FILEPATH/run-list/run-list-${prover}-cav23 $FILEPATH/run-test-result/${prover}/${op}/${op}${no_malloc}_list -twall $TWALL -tcpu $TCPU
$FILEPATH/run-list/run-list-${prover}-cav23 $FILEPATH/run-test-result/$filepathlist -twall $TWALL -tcpu $TCPU
