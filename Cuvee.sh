#!/usr/bin/bash

# cuvee.jar next to this script, such that it runs from any directory, e.g. in BenchExec
java -cp "$(dirname "$0")/cuvee.jar" cuvee.Cuvee "$@"
