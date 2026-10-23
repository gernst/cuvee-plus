// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-zilu/benchmark35_linear.dfy
// SV-COMP loop-zilu/benchmark35_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts up to 10 from a nonnegative value, and x >= 10 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var x: int;
  assume 0 < N;
  tmp₁ := *;
  x := tmp₁;
  if !(x >= 0) {
    result := 0;
    return;
  }
  while x >= 0 && x < N {
    x := x + 1;
  }
  assert x >= N;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
