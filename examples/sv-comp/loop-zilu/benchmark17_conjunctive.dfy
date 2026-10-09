// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark17_conjunctive.dfy
// SV-COMP loop-zilu/benchmark17_conjunctive.yml (expected: safe), translated from the C program
// by hand: i and k count up from 0 together up to an arbitrary n, and k is at least n then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var k: int;
  var n: int;
  i := *;
  k := *;
  n := *;
  assume i == 0 && k == 0;
  while i < n {
    i := i + 1;
    k := k + 1;
  }
  assert k >= n;
}

// remaining goals of -teq -simplify:
// none
