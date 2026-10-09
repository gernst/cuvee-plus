// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/sina4f.dfy
// SV-COMP array-fpi/sina4f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of sina4 with other constants or assertions; checks b[i] == N

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  {
    var i: int, sum: array<int, int>, a: array<int, int>, b: array<int, int>;
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
    i := 0;
    while i < N {
      b := b[i := a[i] + 1];
      i := i + 1;
    }
    i := 0;
    while i < N {
      assert b[i] == N;
      i := i + 1;
    }
    result := 1;
    return;
  }
}
