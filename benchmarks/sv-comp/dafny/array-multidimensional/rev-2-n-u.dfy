// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-multidimensional/rev-2-n-u.dfy
// SV-COMP array-multidimensional/rev-2-n-u.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j]==B[m-i-1][n-j-1]
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  var j: int;
  var m: int;
  var n: int;
  var A: array<int, array<int, int>>;
  var B: array<int, array<int, int>>;
  m := *;
  assume 0 < m;
  n := *;
  assume 0 < n;
  i := 0;
  j := 0;
  while i < m {
    j := 0;
    while j < n {
      tmp₁ := *;
      B := B[i := B[i][j := tmp₁]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while i < m {
    j := 0;
    while j < n {
      A := A[i := A[i][j := B[m - i - 1][n - j - 1]]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while i < m {
    j := 0;
    while j < n {
      assert A[i][j] == B[m - i - 1][n - j - 1];
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
