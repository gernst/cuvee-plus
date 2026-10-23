// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-multidimensional/add-3-n-u.dfy
// SV-COMP array-multidimensional/add-3-n-u.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of add-2-n-u with other constants or assertions; checks
// C[i][j][k]==A[i][j][k]+B[i][j][k]
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500, p for 1800

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var i: int;
  var j: int;
  var k: int;
  var m: int;
  var n: int;
  var p: int;
  var A: array<int, array<int, array<int, int>>>;
  var B: array<int, array<int, array<int, int>>>;
  var C: array<int, array<int, array<int, int>>>;
  m := *;
  assume 0 < m;
  n := *;
  assume 0 < n;
  p := *;
  assume 0 < p;
  i := 0;
  j := 0;
  k := 0;
  while i < m {
    j := 0;
    k := 0;
    while j < n {
      k := 0;
      while k < p {
        tmp₁ := *;
  assume 0 <= tmp₁;
        A := A[i := A[i][j := A[i][j][k := tmp₁]]];
        tmp₂ := *;
  assume 0 <= tmp₂;
        B := B[i := B[i][j := B[i][j][k := tmp₂]]];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while i < m {
    j := 0;
    k := 0;
    while j < n {
      k := 0;
      while k < p {
        C := C[i := C[i][j := C[i][j][k := A[i][j][k] + B[i][j][k]]]];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while i < m {
    j := 0;
    k := 0;
    while j < n {
      k := 0;
      while k < p {
        assert C[i][j][k] == A[i][j][k] + B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
