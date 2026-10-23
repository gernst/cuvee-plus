// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-zilu/benchmark14_linear.dfy
// SV-COMP loop-zilu/benchmark14_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i counts down to 0 from a nonnegative value, and i >= 0 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  tmp₁ := *;
  i := tmp₁;
  if !(i >= 0) {
    result := 0;
    return;
  }
  while i > 0 {
    i := i - 1;
  }
  assert i >= 0;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
