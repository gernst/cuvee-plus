#!/bin/bash
# the quick check of the engine of -prove, each example within 20 seconds, run after each change (see doc/prove.md):
# the examples of trace equation systems in Dafny and C against their expected outputs (./Cuvee.sh -test), two at a
# time (the state examples of the former -teq-state, here before, were removed on Oct 23, 2026); the slow set (the
# algorithms, among them the nested loops and the searches) is in slow.sh
# usage: scripts/prove/quick.sh [jar], from the root of the repository; the jar defaults to cuvee.jar
cd "$(dirname "$0")/../.."
jar=${1:-cuvee.jar}
fails=0
examples=$(ls examples/dafny/teq/*.dfy examples/c/teq/*.c)
for f in $examples; do
  echo "$f"
done | xargs -P 2 -I{} bash -c 'out=$(timeout 20 nice -n 19 java -cp '"$jar"' cuvee.Cuvee -test {} < /dev/null 2>&1); [ "$out" = "ok {}" ] || echo "FAIL {}: $(echo "$out" | head -3)"' | tee /tmp/quick.$$
fails=$(grep -c FAIL /tmp/quick.$$); rm -f /tmp/quick.$$

echo "quick: $(echo $examples | wc -w) examples, $fails failures"
[ "$fails" = 0 ]
