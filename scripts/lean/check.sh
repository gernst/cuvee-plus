#!/usr/bin/bash
# checks the Lean proofs of the lemma database (lean/): the generated statements are those of the current modules
# (with --regenerate, they are regenerated first), and lake builds the proofs without errors and without sorry
set -e
cd "$(dirname "$0")/../.."
if [ "$1" = "--regenerate" ]; then
  python3 scripts/lean/generate.py
else
  python3 scripts/lean/generate.py --check
fi
log=$(mktemp)
trap 'rm -f "$log"' EXIT
if ! "$(elan which lake)" build > "$log" 2>&1; then
  grep -A12 "^error" "$log"
  exit 1
fi
# a cached build does not repeat its warnings, hence the sources are searched
if grep -n -w "sorry\|admit" lean/TEQ/*.lean | grep -v -- "-- "; then
  exit 1
fi
echo "lean: all lemmas of the database proved ($(grep -c '^example' lean/TEQ/Check.lean) lemmas," \
  "$(grep -c '^[a-z]' lean/open.txt) open in lean/open.txt)"
