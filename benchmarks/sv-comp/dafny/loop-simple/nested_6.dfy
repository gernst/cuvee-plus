// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-simple/nested_6.dfy
// SV-COMP loop-simple/nested_6.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_1 with other constants or assertions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6

method main() returns (result: int) {
  var N: int;
  var a: int;
  var b: int;
  var c: int;
  var d: int;
  var e: int;
  var f: int;
  assume 0 < N;
  a := N;
  b := N;
  c := N;
  d := N;
  e := N;
  f := N;
  a := 0;
  while a < N {
    b := 0;
    while b < N {
      c := 0;
      while c < N {
        d := 0;
        while d < N {
          e := 0;
          while e < N {
            f := 0;
            while f < N {
              {}
              f := f + 1;
            }
            e := e + 1;
          }
          d := d + 1;
        }
        c := c + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }
  if !(a == N && b == N && c == N && d == N && e == N && f == N) {
    assert false;
  }
  result := 1;
  return;
}
