// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/multivar_1-1.dfy
// SV-COMP loop-acceleration/multivar_1-1.yml (expected: safe), translated from the C program by
// hand: x and y start equal and are incremented together up to 1024, unsigned in C, nonnegative here
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): x and y are both counters with
// step 1 from the same initial value, over the same iterations
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := *;
  assume 0 <= x;
  y := x;
  while x < N {
    x := x + 1;
    y := y + 1;
  }
  assert x == y;
}

// remaining goals of -teq -simplify:
// none
