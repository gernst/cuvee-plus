// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/copy-partial-2-n-u.dfy
// SV-COMP array-multidimensional/copy-partial-2-n-u.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j]==B[i][j]
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500, q for 500, s for
// 700

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var j: int;
    var m: int;
    var n: int;
    var q: int;
    var s: int;
    var A: array<int, array<int, int>>;
    var B: array<int, array<int, int>>;
    m := *;
    assume 0 < m;
    n := *;
    assume 0 < n;
    q := *;
    assume 0 < q;
    s := *;
    assume 0 < s;
    assume q < m;
    assume s < n;
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
    while i < q {
      j := 0;
      while j < s {
        A := A[i := A[i][j := B[i][j]]];
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    j := 0;
    while i < q {
      j := 0;
      while j < s {
        assert A[i][j] == B[i][j];
        j := j + 1;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}
