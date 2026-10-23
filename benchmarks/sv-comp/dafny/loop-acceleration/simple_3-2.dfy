// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/simple_3-2.dfy
// SV-COMP loop-acceleration/simple_3-2.yml (expected: safe), translated from the C program by
// hand: x counts by 2 up to an arbitrary bound N, an unsigned short, and is even then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): x is counter(0, 2, n), which is
// even

method main() {
  var x: int;
  var N: int;
  x := 0;
  N := *;
  assume 0 <= N;
  while x < N {
    x := x + 2;
  }
  assert rem(x, 2) == 0;
}

// remaining goals of -teq -simplify:
// none
