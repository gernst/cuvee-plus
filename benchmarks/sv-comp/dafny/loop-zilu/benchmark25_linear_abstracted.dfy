// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-zilu/benchmark25_linear_abstracted.dfy
// SV-COMP loop-zilu/benchmark25_linear_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of benchmark02_linear_abstracted with other constants or assertions;
// checks x==10

method main() returns (result: int) {
  var tmp₁: int;
  var x: int;
  tmp₁ := *;
  x := tmp₁;
  if !(x < 0) {
    result := 0;
    return;
  }
  if x < 10 {
    x := *;
    if !(x < 10) {
      assume false;
    }
    if x < 10 {
      x := x + 1;
    }
    if x < 10 {
      assume false;
    }
  }
  assert x == 10;
  result := 0;
  return;
}
