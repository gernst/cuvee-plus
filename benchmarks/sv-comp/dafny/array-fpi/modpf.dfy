// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/modpf.dfy
// SV-COMP array-fpi/modpf.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of modp with other constants or assertions; checks a[i] % N == 1

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
    assert (rem(a[i], N)) == 1;
    i := i + 1;
  }
  result := 1;
  return;
}
