// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_3-1.dfy
// SV-COMP loop-acceleration/simple_3-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of simple_1-1 with other constants or assertions; checks x % 2

method main() returns (result: int) {
  var tmp₁: int;
  var x: int;
  var N: int;
  x := 0;
  tmp₁ := *;
  assume 0 <= tmp₁;
  N := tmp₁;
  while x < N {
    x := x + 2;
  }
  assert (((rem(x, 2))) != 0);
}
