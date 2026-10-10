// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops-crafted-1/nested3-2_abstracted.dfy
// SV-COMP loops-crafted-1/nested3-2_abstracted.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of nested3-1_abstracted with other constants or assertions; checks
// !(z % 4); !(y % 2); !(x % 2)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  var z: int;
  var w: int;
  var z__VERIFIER_LA_tmp0: int;
  var __VERIFIER_LA_iterations0: int;
  var z__VERIFIER_LA_old_tmp0: int;
  assume 0 < N;
  x := 0;
  y := 0;
  z := 0;
  w := 0;
  while x < N {
    y := 0;
    while y < N {
      z := 0;
      if z < N {
        z__VERIFIER_LA_tmp0 := z;
        __VERIFIER_LA_iterations0 := (quot(N - z__VERIFIER_LA_tmp0, 1));
        z__VERIFIER_LA_old_tmp0 := z;
        z := __VERIFIER_LA_iterations0 * 1 + z__VERIFIER_LA_old_tmp0;
      }
      assert !(((rem(z, 4))) != 0);
      y := y + 1;
    }
    assert !(((rem(y, 2))) != 0);
    x := x + 1;
  }
  assert !(((rem(x, 2))) != 0);
  result := 0;
  return;
}
