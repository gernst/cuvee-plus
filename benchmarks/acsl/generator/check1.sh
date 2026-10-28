#!/bin/bash
# check one annotated task with Cuvée (-vcgen -z3): prints "<status>\t<expected verdict>\t<file>\t<output>"
# usage: JAR=<cuvee.jar> TIMEOUT=<s> check1.sh <file>, run from benchmarks/acsl (see check.sh)
G=$(cd "$(dirname "$0")" && pwd)
JAR=${JAR:-$G/../../../cuvee.jar}
f=$1
out=$(timeout ${TIMEOUT:-10} nice -n 19 java -cp "$JAR" cuvee.Cuvee -vcgen -z3 "$f" < /dev/null 2>&1)
rc=$?
verdict=$(grep -A1 'unreach-call.prp' "${f%.*}.yml" | grep -o 'expected_verdict: [a-z]*' | cut -d' ' -f2)
full=$(echo "$out" | tr '\n' ' ' | tr -s ' ')
one=$(echo "$full" | cut -c1-300)
if [ $rc = 124 ]; then st=timeout
elif echo "$full" | grep -q 'incorrect'; then st=refuted
elif echo "$full" | grep -q 'unknown'; then st=unknown
elif echo "$out" | grep -qE '^\(?error|Exception'; then st=error
elif [ $rc != 0 ]; then st=exit$rc
elif echo "$full" | grep -q 'correct'; then st=proved
else st=other; fi
printf '%s\t%s\t%s\t%s\n' "$st" "$verdict" "$f" "$one"
