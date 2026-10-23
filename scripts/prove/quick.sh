#!/bin/bash
# the quick check of the engine of -prove, under 30 seconds, run after each change (see doc/prove.md):
# the state examples against their expected outputs (./Cuvee.sh -test), two at a time; the slow set (the algorithms,
# among them the nested loops and the searches, formerly here) is in slow.sh
# usage: scripts/prove/quick.sh [jar], from the root of the repository; the jar defaults to cuvee.jar
cd "$(dirname "$0")/../.."
jar=${1:-cuvee.jar}
fails=0
state=$(ls examples/dafny/state/*.dfy)
for f in $state; do
  echo "$f"
done | xargs -P 2 -I{} bash -c 'out=$(timeout 20 nice -n 19 java -cp '"$jar"' cuvee.Cuvee -test {} < /dev/null 2>&1); [ "$out" = "ok {}" ] || echo "FAIL {}: $(echo "$out" | head -3)"' | tee /tmp/quick.$$
fails=$(grep -c FAIL /tmp/quick.$$); rm -f /tmp/quick.$$

echo "quick: $(echo $state | wc -w) examples, $fails failures"
[ "$fails" = 0 ]
