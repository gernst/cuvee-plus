// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-multidimensional/init-3-u.dfy
// SV-COMP array-multidimensional/init-3-u.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j][k]==C
// note: the concrete loop bounds are symbolic, arbitrary positive values: n for 1000

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  var j: int;
  var k: int;
  var n: int;
  var A: array<int, array<int, array<int, int>>>;
  var C: int;
  n := *;
  assume 0 < n;
  tmp₁ := *;
  C := tmp₁;
  i := 0;
  j := 0;
  k := 0;
  while i < n {
    j := 0;
    k := 0;
    while j < n {
      k := 0;
      while k < n {
        A := A[i := A[i][j := A[i][j][k := C]]];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while i < n {
    j := 0;
    k := 0;
    while j < n {
      k := 0;
      while k < n {
        assert A[i][j][k] == C;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
