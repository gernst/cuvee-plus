// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/ms4f.dfy
// SV-COMP array-fpi/ms4f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ms4 with other constants or assertions; checks sum[0] > 3*N

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var i: int, sum: array<int, int>, a: array<int, int>;
  N := *;
  if N <= 0 {
    result := 1;
    return;
  }
  i := 0;
  while i < N {
    a := a[i := (rem(i, 4))];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      sum := sum[0 := 0];
    } else {
      sum := sum[0 := sum[0] + a[i]];
    }
    i := i + 1;
  }
  assert sum[0] > 3 * N;
  result := 1;
  return;
}
