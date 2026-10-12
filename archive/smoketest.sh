#!/usr/bin/env bash
# runs Cuvée as in SV-COMP on the examples of this archive: the safe ones are answered correct, the unsafe one
# incorrect, which the tool-info module of BenchExec (cuvee.py) reports as true and false(unreach-call); it also
# checks the bundled z3
cd "$(dirname "$0")" || exit 1
OPTIONS=(-teq -simplify -split -simplify -fallback -z3 -timeout 900000 -verify)

./Cuvee.sh -version || exit 1
./z3 --version || exit 1

for f in examples/safe-*.c; do
  out=$(./Cuvee.sh "${OPTIONS[@]}" "$f" 2>&1) && [ "$out" = correct ] || { echo "$f: not proved"; echo "$out"; exit 1; }
  echo "$f: true"
done

out=$(./Cuvee.sh "${OPTIONS[@]}" examples/unsafe.c 2>&1)
[ "$out" = incorrect ] || { echo "examples/unsafe.c: not refuted"; echo "$out"; exit 1; }
echo "examples/unsafe.c: false"
