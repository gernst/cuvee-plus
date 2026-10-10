// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-lit/cggmp2005.dfy
// SV-COMP loop-lit/cggmp2005.yml (expected: safe), translated from the C program by hand: i
// counts up by 2 from 1, j down by 1 from 10, until they cross, which happens at j == 6
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): i and j are counters with steps
// 2 and -1, the exit is linear in the number of iterations

method main() {
  var i: int;
  var j: int;
  i := 1;
  j := 10;
  while j >= i {
    i := i + 2;
    j := -1 + j;
  }
  assert j == 6;
}

// remaining goals of -teq -simplify:
// none
