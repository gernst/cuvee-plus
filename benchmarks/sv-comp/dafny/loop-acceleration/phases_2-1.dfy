// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/phases_2-1.dfy
// SV-COMP loop-acceleration/phases_2-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of phases_1-1 with other constants or assertions; checks x != y

method main() returns (result: int) {
  var tmp₁: int;
  var x: int;
  var y: int;
  x := 1;
  tmp₁ := *;
  assume 0 <= tmp₁;
  y := tmp₁;
  if !(y > 0) {
    result := 0;
    return;
  }
  while x < y {
    if x < (quot(y, x)) {
      x := x * x;
    } else {
      x := x + 1;
    }
  }
  assert x != y;
}
