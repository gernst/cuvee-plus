// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-multidimensional/transpose-u.dfy
// SV-COMP array-multidimensional/transpose-u.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks C[j][i] == A[i][j]
// note: the concrete loop bounds are symbolic, arbitrary positive values: n for 1000

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  var k: int;
  var j: int;
  var n: int;
  var A: array<int, array<int, int>>;
  var C: array<int, array<int, int>>;
  n := *;
  assume 0 < n;
  i := 0;
  while i < n {
    j := 0;
    while j < n {
      tmp₁ := *;
      A := A[i := A[i][j := tmp₁]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while i < n {
    j := 0;
    while j < n {
      C := C[j := C[j][i := A[i][j]]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < n {
    j := 0;
    while j < n {
      assert C[j][i] == A[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
