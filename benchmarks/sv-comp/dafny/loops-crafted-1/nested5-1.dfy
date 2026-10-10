// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops-crafted-1/nested5-1.dfy
// SV-COMP loops-crafted-1/nested5-1.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of nested3-1 with other constants or assertions; checks v % 4
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455, M for 10

method main() returns (result: int) {
  var N: int;
  var M: int;
  var x: int;
  var y: int;
  var z: int;
  var w: int;
  var v: int;
  assume 0 < N;
  assume 0 < M;
  x := 0;
  y := 0;
  z := 0;
  w := 0;
  v := 0;
  w := 0;
  while w < N {
    x := 0;
    while x < M {
      y := 0;
      while y < M {
        z := 0;
        while z < M {
          v := 0;
          while v < M {
            v := v + 1;
          }
          assert (((rem(v, 4))) != 0);
          z := z + 1;
        }
        y := y + 1;
      }
      x := x + 1;
    }
    w := w + 1;
  }
  result := 0;
  return;
}
