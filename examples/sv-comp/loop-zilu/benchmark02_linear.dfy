// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark02_linear.dfy
// SV-COMP loop-zilu/benchmark02_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i counts from l > 0 to n, and l >= 1 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (the _abstracted variant is the
// same program with an abstracted loop)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int, tmp₃: int;
  var n: int, i: int, l: int;
  tmp₁ := *;
  n := tmp₁;
  tmp₂ := *;
  i := tmp₂;
  tmp₃ := *;
  l := tmp₃;
  i := l;
  if !(l > 0) {
    result := 0;
    return;
  }
  while i < n {
    i := i + 1;
  }
  assert l >= 1;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
