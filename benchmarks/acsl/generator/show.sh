#!/bin/bash
# print the program part of the tasks of a folder, without the harness lines
cd "$(dirname "$0")/../$1"
for f in ${@:2}; do
  v=$(grep -o 'expected_verdict: [a-z]*' ${f%.*}.yml | cut -d' ' -f2)
  echo "##### $f [$v] $(python3 - "$f" <<'PY'
import sys,re
t=open(sys.argv[1]).read()
print(len(re.findall(r'\b(for|while|do)\b', t)), 'loop keywords')
PY
)"
  grep -vE '^\s*$|__assert_fail|^extern |^\s*//|^void reach_error|^void __VERIFIER_assert|ERROR: *\{|^typedef|^#|SPDX|^ *\* |^/\*$|^ \*/$' "$f" | grep -vE '^(void|int) (assume_abort_if_not|__VERIFIER_assume)\(int cond\) \{$|^\s*if \(!cond\) \{ abort\(\); \}$|^\s*if \(!\(cond\)\) \{$' 
done
