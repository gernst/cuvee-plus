#!/bin/bash
# the per-variable form of -teq under -prove against -simplify, by the number of remaining goals (lines starting with
# goal, or asserts in SMT-LIB output for C), on the examples whose command line has -simplify and no module of -teq
# (the fragment lemmas of teq:nested are written for the forms of the simplifier, see
# ideas/deduction-engine-implementation.md); one line per file, the regressions (closed by -simplify only) marked
# usage: scripts/prove/compare.sh [jar] [dirs...], from the root of the repository, one run at a time
cd "$(dirname "$0")/../.."
jar=${1:-cuvee.jar}; shift
dirs=${@:-examples/dafny/teq examples/c/teq}
count() { grep -c "^goal\|^(assert" ; }
for f in $(for d in $dirs; do ls $d/*.dfy $d/*.c 2>/dev/null; done); do
  line=$(head -1 "$f")
  case "$line" in *-simplify*) ;; *) continue;; esac
  case "$line" in *teq:*) continue;; esac
  args=$(echo "$line" | sed 's|^// ./Cuvee.sh ||' | sed "s| $f||")
  args_=$(echo "$args" | sed 's| -simplify| -prove|g; s|^-simplify|-prove|')
  s=$(timeout 60 nice -n 19 java -cp "$jar" cuvee.Cuvee $args "$f" < /dev/null 2>/dev/null | count); cs=$?
  start=$(date +%s)
  p=$(timeout 60 nice -n 19 java -cp "$jar" cuvee.Cuvee $args_ "$f" < /dev/null 2>/dev/null | count)
  t=$(( $(date +%s) - start ))
  mark=""; [ "$s" -lt "$p" ] && mark=" REGRESSION"; [ "$s" -gt "$p" ] && mark=" better"
  echo "$f: simplify $s, prove $p, $t s$mark"
done
