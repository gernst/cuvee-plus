// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/nested_1-1.dfy
// SV-COMP loop-acceleration/nested_1-1.yml (expected: safe), translated from the C program by
// hand: x counts up to 268435455 (0x0fffffff), which is odd, while an inner loop counts y from 0 to 10 in each
// iteration
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the inner loop is summarized, it
// does not affect x, which is a counter that exits at 268435455
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 268435455, which is odd,
// M for 10

method main() {
  var N: int;
  var M: int;
  var x: int;
  var y: int;
  assume 0 < N && rem(N, 2) == 1;
  assume 0 < M;
  x := 0;
  y := 0;
  while x < N {
    y := 0;
    while y < M {
      y := y + 1;
    }
    x := x + 1;
  }
  assert rem(x, 2) != 0;
}

// remaining goals of -teq -simplify:
// none
