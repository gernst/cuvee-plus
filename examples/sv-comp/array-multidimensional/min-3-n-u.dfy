// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/min-3-n-u.dfy
// SV-COMP ReachSafety-Arrays/array-multidimensional/min-3-n-u.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j][k]>=min
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500, p for 1800

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var j: int;
    var k: int;
    var m: int;
    var n: int;
    var p: int;
    var A: array<int, array<int, array<int, int>>>;
    var min: int;
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
          A := A[i := A[i][j := A[i][j][k := tmp₁]]];
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    j := 0;
    k := 0;
    min := A[0][0][0];
    while i < m {
      j := 0;
      k := 0;
      while j < n {
        k := 0;
        while k < p {
          if A[i][j][k] < min {
            min := A[i][j][k];
          }
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
          assert A[i][j][k] >= min;
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
