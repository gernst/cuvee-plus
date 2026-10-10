// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/brs2f.dfy
// SV-COMP array-fpi/brs2f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of brs2 with other constants or assertions; checks sum[0] <= 2*N

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
    if (rem(i, 2)) == 0 {
      a := a[i := 20];
    } else {
      a := a[i := 0];
    }
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
  assert sum[0] <= 2 * N;
  result := 1;
  return;
}
