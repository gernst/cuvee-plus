// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/simple_2-2.dfy
// SV-COMP loop-acceleration/simple_2-2.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of simple_1-1 with other constants or assertions; checks x > 0x0fffffff
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var x: int;
  assume 0 < N;
  tmp₁ := *;
  assume 0 <= tmp₁;
  x := tmp₁;
  while x < N {
    x := x + 1;
  }
  assert x > N;
}
