// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-new/count_by_2.dfy
// SV-COMP ReachSafety-Loops/loop-new/count_by_2.yml (expected: safe), translated from the C program by hand: i
// counts by 2 up to 1000000, which it hits exactly
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): i is counter(0, 2, n), the
// iteration constraint over earlier values bounds n, and the exit gives i == 1000000

method main() {
  var i: int;
  i := 0;
  while i < 1000000 {
    i := i + 2;
  }
  assert i == 1000000;
}

// remaining goals of -teq -simplify:
// none
