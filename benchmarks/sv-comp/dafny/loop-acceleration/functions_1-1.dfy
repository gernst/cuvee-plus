// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/functions_1-1.dfy
// SV-COMP loop-acceleration/functions_1-1.yml (expected: safe), translated from the C program by
// hand: x is updated by f(x) = x + 2 up to 268435455 (0x0fffffff), and is even then
//
// findings: the call of f is inlined, as by verification tools, the update is x + 2, which teq.dfy accelerates to
// counter(0, 2, n); closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() {
  var N: int;
  var x: int;
  assume 0 < N;
  x := 0;
  while x < N {
    x := x + 2;
  }
  assert rem(x, 2) == 0;
}

// remaining goals of -teq -simplify:
// none
