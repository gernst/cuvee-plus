// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/diff-2-n-u.dfy
// SV-COMP array-multidimensional/diff-2-n-u.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks C[i][j]==A[i][j]-B[i][j]
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: int;
  {
    var i: int;
    var j: int;
    var m: int;
    var n: int;
    var A: array<int, array<int, int>>;
    var B: array<int, array<int, int>>;
    var C: array<int, array<int, int>>;
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
    assume 0 <= tmp₁;
        A := A[i := A[i][j := tmp₁]];
        tmp₂ := *;
    assume 0 <= tmp₂;
        B := B[i := B[i][j := tmp₂]];
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    j := 0;
    while i < m {
      j := 0;
      while j < n {
        tmp₃ := *;
    assume 0 <= tmp₃;
        A := A[i := A[i][j := tmp₃]];
        tmp₄ := *;
    assume 0 <= tmp₄;
        B := B[i := B[i][j := tmp₄]];
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    j := 0;
    while i < m {
      j := 0;
      while j < n {
        C := C[i := C[i][j := A[i][j] - B[i][j]]];
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    j := 0;
    while i < m {
      j := 0;
      while j < n {
        assert C[i][j] == A[i][j] - B[i][j];
        j := j + 1;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}
