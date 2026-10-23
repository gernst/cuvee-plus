// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/nested3-1_abstracted.dfy
// SV-COMP loops-crafted-1/nested3-1_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks z % 4; y % 2; x % 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455
// note: assumes N odd, as the C version: the property depends on the original constant, which the symbolic bound
// generalizes, and fails without (benchmarks/sv-comp/c/false-verdicts.md, group 1)

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  var z: int;
  var w: int;
  assume 0 < N && rem(N, 2) == 1;
  x := 0;
  y := 0;
  z := 0;
  w := 0;
  while x < N {
    y := 0;
    while y < N {
      z := 0;
      if z < N {
        z := *;
  assume 0 <= z;
        if !(z < N) {
          assume false;
        }
        if z < N {
          z := z + 1;
        }
        if z < N {
          assume false;
        }
      }
      assert (((rem(z, 4))) != 0);
      y := y + 1;
    }
    assert (((rem(y, 2))) != 0);
    x := x + 1;
  }
  assert (((rem(x, 2))) != 0);
  result := 0;
  return;
}
