#!/bin/bash

#Remove polished_tests
./clean.sh

#Create clean files into polished_tests
python3 convert_cav23.py
python3 convert_crafted.py

#Runs all provers on all files
#Outputs results as log-files in run-test-result
run-list/run-all-cav23.sh 300 2700 0 all 42 


