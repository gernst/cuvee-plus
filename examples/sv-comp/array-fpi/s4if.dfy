// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/s4if.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/s4if.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of s12if with other constants or assertions; checks sum[0] == 4*N

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  {
    var i: int, sum: array<int, int>, a: array<int, int>;
    N := *;
    if N <= 0 {
      result := 1;
      return;
    }
    assume N <= 536870911;
    sum := sum[0 := 0];
    i := 0;
    while i < N {
      a := a[i := 4];
      i := i + 1;
    }
    i := 0;
    while i < N {
      if a[i] == 4 {
        sum := sum[0 := sum[0] + a[i]];
      } else {
        sum := sum[0 := sum[0] * a[i]];
      }
      i := i + 1;
    }
    assert sum[0] == 4 * N;
    result := 1;
    return;
  }
}
