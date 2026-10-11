#!/usr/bin/env bash
# runs Cuvée as in SV-COMP on the examples of this archive: the safe ones are proved (no output, exit code 0),
# the unsafe one has a goal that simplifies to false, which the tool-info module of BenchExec (cuvee.py) reports as
# false(unreach-call); it also checks the bundled z3, which the unsafe example passes its goal to
cd "$(dirname "$0")" || exit 1
OPTIONS=(-teq -simplify -split -simplify -fallback -z3 -timeout 900000)

./Cuvee.sh -version || exit 1
./z3 --version || exit 1

for f in examples/safe-*.c; do
  out=$(./Cuvee.sh "${OPTIONS[@]}" "$f" 2>&1) && [ -z "$out" ] || { echo "$f: not proved"; echo "$out"; exit 1; }
  echo "$f: true"
done

out=$(./Cuvee.sh "${OPTIONS[@]}" examples/unsafe.c 2>&1)
echo "$out" | tr -s ' \n' ' ' | grep -qE '"goal does not hold" "Sat" "false"|\(goal false\)' \
  || { echo "examples/unsafe.c: not refuted"; echo "$out"; exit 1; }
echo "examples/unsafe.c: false"
