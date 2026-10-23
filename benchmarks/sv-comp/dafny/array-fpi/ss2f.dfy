// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/ss2f.dfy
// SV-COMP array-fpi/ss2f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ss2 with other constants or assertions; checks a[i] == N*(N+2)

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
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + sum[0]];
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
    assert a[i] == N * (N + 2);
    i := i + 1;
  }
  result := 1;
  return;
}
