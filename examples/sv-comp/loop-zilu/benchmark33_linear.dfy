// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark33_linear.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark33_linear.yml (expected: safe), translated from the C program by
// hand: x counts up from a nonnegative value to 100 at least
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  havoc x;
  assume x >= 0;
  while x < 100 && x >= 0 {
    x := x + 1;
  }
  assert x >= 100;
}

// remaining goals of -teq -simplify:
// none
