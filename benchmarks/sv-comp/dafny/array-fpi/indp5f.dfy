// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/indp5f.dfy
// SV-COMP array-fpi/indp5f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of indp5 with other constants or assertions; checks sum[0] == N

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var i: int, a: array<int, int>, sum: array<int, int>;
  N := *;
  if N <= 0 {
    result := 1;
    return;
  }
  sum := sum[0 := 1];
  i := 0;
  while i < N {
    a := a[i := (i + 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] - i * i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] - i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] - i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  assert sum[0] == N;
  result := 1;
  return;
}
