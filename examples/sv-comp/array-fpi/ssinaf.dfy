// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ssinaf.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ssinaf.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ssina with other constants or assertions; checks a[i] == (N+1) * (N+1)

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
      a := a[i := 1];
      i := i + 1;
    }
    i := 0;
    while i < N {
      sum := sum[0 := sum[0] + a[i]];
      i := i + 1;
    }
    i := 0;
    while i < N {
      a := a[i := a[i] + sum[0]];
      i := i + 1;
    }
    sum := sum[0 := 1];
    i := 0;
    while i < N {
      sum := sum[0 := sum[0] + a[i]];
      i := i + 1;
    }
    i := 0;
    while i < N {
      a := a[i := a[i] + sum[0]];
      i := i + 1;
    }
    i := 0;
    while i < N {
      assert a[i] == (N + 1) * (N + 1);
      i := i + 1;
    }
    result := 1;
    return;
  }
}
