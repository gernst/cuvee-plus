// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/rev-3-u.dfy
// SV-COMP ReachSafety-Arrays/array-multidimensional/rev-3-u.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j][k]==B[n-i-1][n-j-1][n-k-1]
// note: the concrete loop bounds are symbolic, arbitrary positive values: n for 1000

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var j: int;
    var k: int;
    var n: int;
    var A: array<int, array<int, array<int, int>>>;
    var B: array<int, array<int, array<int, int>>>;
    n := *;
    assume 0 < n;
    i := 0;
    j := 0;
    k := 0;
    while i < n {
      j := 0;
      k := 0;
      while j < n {
        k := 0;
        while k < n {
          tmp₁ := *;
          B := B[i := B[i][j := B[i][j][k := tmp₁]]];
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
          A := A[i := A[i][j := A[i][j][k := B[n - i - 1][n - j - 1][n - k - 1]]]];
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
          assert A[i][j][k] == B[n - i - 1][n - j - 1][n - k - 1];
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}
