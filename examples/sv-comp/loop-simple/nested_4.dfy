// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_4.dfy
// SV-COMP loop-simple/nested_4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_1 with other constants or assertions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6

method main() returns (result: int) {
  var N: int;
  var a: int;
  var b: int;
  var c: int;
  var d: int;
  assume 0 < N;
  a := N;
  b := N;
  c := N;
  d := N;
  a := 0;
  while a < N {
    b := 0;
    while b < N {
      c := 0;
      while c < N {
        d := 0;
        while d < N {
          {}
          d := d + 1;
        }
        c := c + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }
  if !(a == N && b == N && c == N && d == N) {
    assert false;
  }
  result := 1;
  return;
}
