#!/bin/bash
# the slow sets of the engine of -prove, run on request or before a commit, not in between (see quick.sh):
# the unit tests and the algorithms of examples/dafny/algorithms with their command lines, each with a
# 60 s timeout, two at a time, reporting the exit status, the time and the number of remaining goals per file, as the
# baseline for the work on the algorithms (most leave goals or fail, since teq.dfy lacks their lemmas and the optional
# modules they include were written for the per-variable form)
# usage: scripts/prove/slow.sh [jar], from the root of the repository
cd "$(dirname "$0")/../.."
jar=${1:-cuvee.jar}

mill -i test.testOnly cuvee.test.prove.SimplexTests cuvee.test.prove.ClassesTests < /dev/null 2>&1 | grep "Tests:"

one() {
  f=$1; jar=$2
  args=$(head -1 "$f" | sed 's|^// ./Cuvee.sh ||' | sed "s| $f||")
  start=$(date +%s)
  out=$(timeout 60 nice -n 19 java -cp "$jar" cuvee.Cuvee $args "$f" < /dev/null 2>&1)
  code=$?
  goals=$(echo "$out" | grep -c "^goal")
  error=$(echo "$out" | grep -m1 "^error\|^Exception" | cut -c1-80)
  printf "%s: exit %s, %s s, goals %s %s\n" "$(basename $f .dfy)" "$code" "$(( $(date +%s) - start ))" "$goals" "$error"
}
export -f one
ls examples/dafny/algorithms/*.dfy | xargs -P 2 -I{} bash -c 'one {} '"$jar" | sort
