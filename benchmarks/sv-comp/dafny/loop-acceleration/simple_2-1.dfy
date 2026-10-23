// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/simple_2-1.dfy
// SV-COMP loop-acceleration/simple_2-1.yml (expected: safe), translated from the C program by
// hand: an arbitrary x >= 0 (unsigned) is increased while below 0x0fffffff, and checked to be at least that
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() {
  var N: int;
  var x: int;
  assume 0 < N;
  x := *;
  assume x >= 0;
  while x < N {
    x := x + 1;
  }
  assert x >= N;
}

// remaining goals of -teq -simplify:
// none
