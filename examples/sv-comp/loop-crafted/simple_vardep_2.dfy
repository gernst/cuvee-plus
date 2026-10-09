// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_vardep_2.dfy
// SV-COMP ReachSafety-Loops/loop-crafted/simple_vardep_2.yml (expected: safe), translated from the C program by
// hand: as simple_vardep_1, with k == 3 i and j == 2 i checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var j: int;
  var k: int;
  i := 0;
  j := 0;
  k := 0;
  while k < 268435455 {
    i := i + 1;
    j := j + 2;
    k := k + 3;
    assert k == 3 * i && j == 2 * i;
  }
}

// remaining goals of -teq -simplify:
// none
