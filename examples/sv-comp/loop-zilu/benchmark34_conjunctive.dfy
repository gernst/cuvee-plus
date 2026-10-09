// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark34_conjunctive.dfy
// SV-COMP loop-zilu/benchmark34_conjunctive.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: j counts up to n and k down, and k == 0 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int, tmp₃: int;
  var j: int, k: int, n: int;
  tmp₁ := *;
  j := tmp₁;
  tmp₂ := *;
  k := tmp₂;
  tmp₃ := *;
  n := tmp₃;
  if !(j == 0 && k == n > 0) {
    result := 0;
    return;
  }
  while j < n && n > 0 {
    j := j + 1;
    k := k - 1;
  }
  assert k == 0;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
