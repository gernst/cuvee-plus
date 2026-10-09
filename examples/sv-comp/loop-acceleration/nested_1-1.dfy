// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/nested_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/nested_1-1.yml (expected: safe), translated from the C program by
// hand: x counts up to 268435455 (0x0fffffff), which is odd, while an inner loop counts y from 0 to 10 in each
// iteration
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the inner loop is summarized, it
// does not affect x, which is a counter that exits at 268435455

method main() {
  var x: int;
  var y: int;
  x := 0;
  y := 0;
  while x < 268435455 {
    y := 0;
    while y < 10 {
      y := y + 1;
    }
    x := x + 1;
  }
  assert x % 2 != 0;
}

// remaining goals of -teq -simplify:
// none
