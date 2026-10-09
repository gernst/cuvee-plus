// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark23_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark23_conjunctive.yml (expected: safe), translated from the C program
// by hand: j counts by 2 while i counts to 100, and j is 200 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var j: int;
  havoc i;
  havoc j;
  assume i == 0 && j == 0;
  while i < 100 {
    j := j + 2;
    i := i + 1;
  }
  assert j == 200;
}

// remaining goals of -teq -simplify:
// none
