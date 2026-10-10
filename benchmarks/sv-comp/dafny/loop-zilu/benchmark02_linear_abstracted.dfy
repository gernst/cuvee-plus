// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-zilu/benchmark02_linear_abstracted.dfy
// SV-COMP loop-zilu/benchmark02_linear_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks l>=1

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var n: int;
  var i: int;
  var l: int;
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
  if i < n {
    i := *;
  }
  if i < n {
    assume false;
  }
  assert l >= 1;
  result := 0;
  return;
}
