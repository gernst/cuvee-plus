#!/bin/bash
# the quick check of the engine of -prove, under 30 seconds, run after each change (see doc/prove.md):
# the state examples except the transpose against their expected outputs (./Cuvee.sh -test), two at a time,
# and four examples of the per-variable form of -teq under -prove, which must leave no goal;
# the slow sets (the transpose, the algorithms in the state form, the comparison with -simplify) are in slow.sh
# usage: scripts/prove/quick.sh [jar], from the root of the repository; the jar defaults to cuvee.jar
cd "$(dirname "$0")/../.."
jar=${1:-cuvee.jar}
fails=0
state=$(ls examples/dafny/state/*.dfy | grep -v transpose)
for f in $state; do
  echo "$f"
done | xargs -P 2 -I{} bash -c 'out=$(timeout 20 nice -n 19 java -cp '"$jar"' cuvee.Cuvee -test {} < /dev/null 2>&1); [ "$out" = "ok {}" ] || echo "FAIL {}: $(echo "$out" | head -3)"' | tee /tmp/quick.$$
fails=$(grep -c FAIL /tmp/quick.$$); rm -f /tmp/quick.$$

pervar="examples/dafny/teq/counter.dfy examples/dafny/teq/swap.dfy examples/dafny/teq/copy.dfy examples/dafny/teq/bsearch.dfy"
for f in $pervar; do echo "$f"; done | xargs -P 2 -I{} bash -c 'goals=$(timeout 20 nice -n 19 java -cp '"$jar"' cuvee.Cuvee -teq -prove {} < /dev/null 2>&1 | grep -c "^goal"); [ "$goals" = 0 ] || echo "FAIL {}: $goals goals under -teq -prove"' | tee /tmp/quick.$$
fails=$((fails + $(grep -c FAIL /tmp/quick.$$))); rm -f /tmp/quick.$$

echo "quick: $(echo $state | wc -w) state examples and 4 per-variable examples, $fails failures"
[ "$fails" = 0 ]
