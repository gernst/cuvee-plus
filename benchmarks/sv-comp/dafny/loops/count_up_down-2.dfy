// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/count_up_down-2.dfy
// SV-COMP loops/count_up_down-2.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of count_up_down-1 with other constants or assertions; checks y!=n

method main() returns (result: int) {
  var tmp₁: int;
  var n: int;
  var x: int;
  var y: int;
  tmp₁ := *;
  assume 0 <= tmp₁;
  n := tmp₁;
  x := n;
  y := 0;
  while x > 0 {
    x := x - 1;
    y := y + 1;
  }
  assert y != n;
}
