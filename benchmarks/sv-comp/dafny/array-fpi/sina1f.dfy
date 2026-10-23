// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/sina1f.dfy
// SV-COMP array-fpi/sina1f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of sina1 with other constants or assertions; checks a[i] == N

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
  sum := sum[0 := 1];
  i := 0;
  while i < N {
    sum := sum[0 := sum[0] + 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := sum[0]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N;
    i := i + 1;
  }
  result := 1;
  return;
}
