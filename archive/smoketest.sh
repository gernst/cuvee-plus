#!/usr/bin/env bash
# runs Cuvée on the examples of this archive and checks its answers (option -verify): correct for the safe ones,
# incorrect for the unsafe ones, which the tool-info module of BenchExec (cuvee.py) reports as true and false; it
# covers trace equation systems with and without the fallback to z3 (the configuration of SV-COMP) and constrained
# Horn clauses, on C programs and SV-LIB scripts, in parallel with a solver timeout of 10 s, and checks the version
# and the bundled z3; exit code 0 if all answers are as expected
cd "$(dirname "$0")" || exit 1

TEQ=(-teq -simplify -split -simplify)
FALLBACK=(-teq -simplify -split -simplify -fallback -z3)
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
  ./Cuvee.sh "$@" -timeout 10000 -verify "examples/$file" > "$result.answer" 2>&1 < /dev/null &
}

count=0
check incorrect unsafe.c "${TEQ[@]}"
check correct safe-array.c "${FALLBACK[@]}"
check correct safe-nested.c "${FALLBACK[@]}"
check correct safe-loop.c "${CHC[@]}"
check correct safe-add.svlib "${CHC[@]}"
check incorrect unsafe-add.svlib "${CHC[@]}"
wait

failed=0
for ((i = 0; i < count; i++)); do
  read -r expected file options < "$out/$i.check"
  answer=$(cat "$out/$i.answer")
  if [ "$answer" = "$expected" ]; then
    echo "$file ($options): $expected"
  else
    echo "$file ($options): expected $expected, got:"
    echo "$answer"
    failed=1
  fi
done

exit $failed
