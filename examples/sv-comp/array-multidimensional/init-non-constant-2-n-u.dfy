// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/init-non-constant-2-n-u.dfy
// SV-COMP array-multidimensional/init-non-constant-2-n-u.yml (expected: safe), translated from
// the C program by ./Cuvee.sh -print dfy: a program of the folder; checks A[i][j]==i+j+C

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
    var C: int;
    m := 1000;
    n := 1500;
    tmp₁ := *;
    assume 0 <= tmp₁;
    C := tmp₁;
    q := *;
    s := *;
    i := 0;
    j := 0;
    assume q < m;
    assume s < n;
    while i < q {
      j := 0;
      while j < s {
        A := A[i := A[i][j := i + j + C]];
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    j := 0;
    while i < q {
      j := 0;
      while j < s {
        assert A[i][j] == i + j + C;
        j := j + 1;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}
