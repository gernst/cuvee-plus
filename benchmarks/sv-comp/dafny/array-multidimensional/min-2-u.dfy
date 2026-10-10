// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-multidimensional/min-2-u.dfy
// SV-COMP array-multidimensional/min-2-u.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j]>=min
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  var j: int;
  var m: int;
  var n: int;
  var A: array<int, array<int, int>>;
  var min: int;
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
      A := A[i := A[i][j := tmp₁]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  min := A[0][0];
  while i < n {
    j := 0;
    while j < n {
      if A[i][j] < min {
        min := A[i][j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while i < n {
    j := 0;
    while j < n {
      assert A[i][j] >= min;
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
