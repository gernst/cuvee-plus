#!/usr/bin/bash

# cuvee.jar next to this script, such that it runs from any directory, e.g. in BenchExec
# z3 next to this script first, if any, e.g. in BenchExec, whose machines have no z3 (see cuvee.py)
PATH="$(dirname "$0"):$PATH" java -cp "$(dirname "$0")/cuvee.jar" cuvee.Cuvee "$@"
