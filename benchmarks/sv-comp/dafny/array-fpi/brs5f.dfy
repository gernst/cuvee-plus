// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/brs5f.dfy
// SV-COMP array-fpi/brs5f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of brs5 with other constants or assertions; checks sum[0] <= 5*N

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var check_size: int, i: int, sum: array<int, int>, a: array<int, int>;
  N := *;
  if N <= 0 {
    result := 1;
    return;
  }
  check_size := if 4 > 5 then 4 else 5;
  i := 0;
  while i < N {
    if (rem(i, 5)) == 0 {
      a := a[i := 5];
    } else {
      a := a[i := 5];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      sum := sum[0 := N + 5];
    } else {
      sum := sum[0 := sum[0] + a[i]];
    }
    i := i + 1;
  }
  assert sum[0] <= 5 * N;
  result := 1;
  return;
}
