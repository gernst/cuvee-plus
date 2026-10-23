#!/usr/bin/env bash
# runs Cuvée on the examples of this archive and checks its verdicts (option -quiet, which prints only the answers):
# correct for the safe ones, incorrect for the unsafe ones, combined from the answers as the tool-info module of
# BenchExec (cuvee.py) does, which reports them as true and false; it covers trace equation systems with the lemma database, with and without the fallback to z3 (the
# configurations of SV-COMP), and constrained Horn clauses, each on a safe and an unsafe C program and SV-LIB script, in
# parallel with a solver timeout of 10 s, and checks the version and the bundled z3; exit code 0 if all answers are as
# expected
cd "$(dirname "$0")" || exit 1

MODULES=(-include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters
  -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned)
TEQ=(-teq "${MODULES[@]}" -prove -split -prove -split -prove)
FALLBACK=("${TEQ[@]}" -fallback -z3)
CHC=(-chc -z3)

./Cuvee.sh -version || exit 1
./z3 --version || exit 1

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

# check <expected answer> <file> <options...>, in the background: the answer is compared once all checks are done
check() {
  local expected=$1 file=$2
  shift 2
  local result="$out/$((count++))"
  echo "$expected $file $*" > "$result.check"
  ./Cuvee.sh "$@" -timeout 10000 -quiet "examples/$file" > "$result.answer" 2>&1 < /dev/null &
}

count=0
check correct safe-array.c "${TEQ[@]}"
check incorrect unsafe.c "${TEQ[@]}"
check correct safe-add.svlib "${TEQ[@]}"
check incorrect unsafe-add.svlib "${TEQ[@]}"
check correct safe-nested.c "${FALLBACK[@]}"
check incorrect unsafe.c "${FALLBACK[@]}"
check correct safe-add.svlib "${FALLBACK[@]}"
check incorrect unsafe-add.svlib "${FALLBACK[@]}"
check correct safe-loop.c "${CHC[@]}"
check incorrect unsafe.c "${CHC[@]}"
check correct safe-add.svlib "${CHC[@]}"
check incorrect unsafe-add.svlib "${CHC[@]}"
wait

failed=0
for ((i = 0; i < count; i++)); do
  read -r expected file options < "$out/$i.check"
  # one answer per goal, among other output (the model of -chc), of which an incorrect one decides, and all must be
  # correct for the verdict correct
  answers=$(grep -x -E 'correct|incorrect|unknown' "$out/$i.answer" | sort -u)
  if grep -qx incorrect <<< "$answers"; then
    answer=incorrect
  elif [ "$answers" = correct ]; then
    answer=correct
  else
    answer=unknown
  fi
  if [ "$answer" = "$expected" ]; then
    echo "$file ($options): $expected"
  else
    echo "$file ($options): expected $expected, got $answer:"
    cat "$out/$i.answer"
    failed=1
  fi
done

exit $failed
