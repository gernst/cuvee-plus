// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/nested3-2.dfy
// SV-COMP loops-crafted-1/nested3-2.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of nested3-1 with other constants or assertions; checks !(z % 4); !(y % 2); !(x
// % 2)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  var z: int;
  var w: int;
  assume 0 < N;
  x := 0;
  y := 0;
  z := 0;
  w := 0;
  while x < N {
    y := 0;
    while y < N {
      z := 0;
      while z < N {
        z := z + 1;
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
