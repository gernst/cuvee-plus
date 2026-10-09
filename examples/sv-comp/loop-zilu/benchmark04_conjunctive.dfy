// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-zilu/benchmark04_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark04_conjunctive.yml (expected: safe), translated from the C program
// by hand: j counts up from 0 to n, k down from at least n, and k is nonnegative then
//
// findings: the iteration constraint bounds the values of k, a counter with step -1 among three dependencies, which
// teq.dfy does not accelerate; the lemma states that a lower bound of a counter with an arbitrary step holds in all
// iterations iff it holds at both ends, and -split splits the resulting disjunction; closed (no output). Attempt:
// the bound as b < x does not match k < x + n (see TODO.md), as 0 < x + c it does
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var k: int;
  var j: int;
  var n: int;
  havoc k;
  havoc j;
  havoc n;
  assume n >= 1 && k >= n && j == 0;
  while j <= n - 1 {
    j := j + 1;
    k := k - 1;
  }
  assert k >= 0;
}

// remaining goals of -teq -simplify -split -simplify:
// none
