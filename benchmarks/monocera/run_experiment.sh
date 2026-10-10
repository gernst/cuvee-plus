#!/bin/bash

#Remove polished_tests
./clean.sh

if [[ "$#" -ne "3" ]] 
then
	echo 'Needs three params in correct order:' 
	echo '  1: (monocera/tricera/seahorn/cpa/all) which prover to use'
	echo '  2: timeout in seconds'
	echo '  3: number of tests to run per operator and tool, 0 to run all available tests'
	exit 1
fi

#######Inputs#################
# TOOL is the tool to run in the experiments, can either be a 
# single tool (monocera / tricera / seahorn / cpa) or 'all',
# in which case all provers will be run. 
TOOL=${1:-"all"}	
#WallTO is Walltimeout in seconds
WALLTO=${2:-"300"}
#NRTESTS is number of tests per operator (0 for all tests)
NRTESTS=${3:-"0"}

#Create clean files into polished_tests
python3 convert_cav23.py
python3 convert_crafted.py

#Runs all provers on all files
#Outputs results as log-files in run-test-result
let "CPUTO = $WALLTO * 9"
run-list/run-all-cav23.sh $WALLTO $CPUTO $NRTESTS $TOOL 42 
