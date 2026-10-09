// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/nested6.dfy
// SV-COMP loop-invgen/nested6.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks k>=2*i; k >= n; k <= n

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var j: int;
    var k: int;
    var n: int;
    k := *;
    n := *;
    if !(n < 1000000) {
      result := 0;
      return;
    }
    if k == n {} else {
      result := 0;
      return;
    }
    i := 0;
    while i < n {
      j := 2 * i;
      while j < n {
        tmp₁ := *;
        if (tmp₁ != 0) {
          k := j;
          while k < n {
            assert k >= 2 * i;
            k := k + 1;
          }
        } else {
          assert k >= n;
          assert k <= n;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}
