// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark26_linear.dfy
// SV-COMP loop-zilu/benchmark26_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts up to y, and x == y is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (the _abstracted variant is the
// same program with an abstracted loop)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int;
  var x: int, y: int;
  tmp₁ := *;
  x := tmp₁;
  tmp₂ := *;
  y := tmp₂;
  if !(x < y) {
    result := 0;
    return;
  }
  while x < y {
    x := x + 1;
  }
  assert x == y;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
