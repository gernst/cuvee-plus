// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/init-4-n-u.dfy
// SV-COMP ReachSafety-Arrays/array-multidimensional/init-4-n-u.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of init-2-n-u with other constants or assertions; checks A[i][j][k][l]==C
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500, p for 1800, q for
// 2000

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var j: int;
    var k: int;
    var l: int;
    var m: int;
    var n: int;
    var p: int;
    var q: int;
    var A: array<int, array<int, array<int, array<int, int>>>>;
    var C: int;
    m := *;
    assume 0 < m;
    n := *;
    assume 0 < n;
    p := *;
    assume 0 < p;
    q := *;
    assume 0 < q;
    tmp₁ := *;
    C := tmp₁;
    i := 0;
    j := 0;
    k := 0;
    l := 0;
    while i < m {
      j := 0;
      k := 0;
      l := 0;
      while j < n {
        k := 0;
        l := 0;
        while k < p {
          l := 0;
          while l < q {
            A := A[i := A[i][j := A[i][j][k := A[i][j][k][l := C]]]];
            l := l + 1;
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
    l := 0;
    while i < m {
      j := 0;
      k := 0;
      l := 0;
      while j < n {
        k := 0;
        l := 0;
        while k < p {
          l := 0;
          while l < q {
            assert A[i][j][k][l] == C;
            l := l + 1;
          }
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
