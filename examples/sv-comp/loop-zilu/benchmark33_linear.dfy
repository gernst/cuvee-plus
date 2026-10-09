// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark33_linear.dfy
// SV-COMP loop-zilu/benchmark33_linear.yml (expected: safe), translated from the C program by
// hand: x counts up from a nonnegative value to 100 at least
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100

method main() {
  var N: int;
  var x: int;
  assume 0 < N;
  x := *;
  assume x >= 0;
  while x < N && x >= 0 {
    x := x + 1;
  }
  assert x >= N;
}

// remaining goals of -teq -simplify:
// none
