// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/condgf.dfy
// SV-COMP array-fpi/condgf.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of condg with other constants or assertions; checks a[i] == 0

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
      a := a[i := 2];
      i := i + 1;
    }
    i := 0;
    while i < N {
      sum := sum[0 := sum[0] + a[i]];
      i := i + 1;
    }
    i := 0;
    while i < N {
      if sum[0] == N {
        a := a[i := a[i] - 1];
      } else {
        a := a[i := a[i] + 1];
      }
      i := i + 1;
    }
    i := 0;
    while i < N {
      assert a[i] == 0;
      i := i + 1;
    }
    result := 1;
    return;
  }
}
