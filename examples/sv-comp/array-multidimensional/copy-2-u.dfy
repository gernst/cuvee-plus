// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/copy-2-u.dfy
// SV-COMP array-multidimensional/copy-2-u.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j]==B[i][j]
// note: the concrete loop bounds are symbolic, arbitrary positive values: n for 1000

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  var j: int;
  var n: int;
  var A: array<int, array<int, int>>;
  var B: array<int, array<int, int>>;
  n := *;
  assume 0 < n;
  i := 0;
  j := 0;
  while i < n {
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
  while i < n {
    j := 0;
    while j < n {
      A := A[i := A[i][j := B[i][j]]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while i < n {
    j := 0;
    while j < n {
      assert A[i][j] == B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
