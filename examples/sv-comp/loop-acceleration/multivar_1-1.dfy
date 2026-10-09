// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/multivar_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/multivar_1-1.yml (expected: safe), translated from the C program by
// hand: x and y start equal and are incremented together up to 1024, unsigned in C, nonnegative here
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): x and y are both counters with
// step 1 from the same initial value, over the same iterations

method main() {
  var x: int;
  var y: int;
  x := *;
  assume 0 <= x;
  y := x;
  while x < 1024 {
    x := x + 1;
    y := y + 1;
  }
  assert x == y;
}

// remaining goals of -teq -simplify:
// none
