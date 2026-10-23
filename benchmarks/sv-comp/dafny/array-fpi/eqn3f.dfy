// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/eqn3f.dfy
// SV-COMP array-fpi/eqn3f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of eqn3 with other constants or assertions; checks b[i] == 3*i*i + 3*i + 1

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var i: int, a: array<int, int>, b: array<int, int>;
  N := *;
  if N <= 0 {
    result := 1;
    return;
  }
  a := a[0 := 6];
  b := b[0 := 10];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 6];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == 3 * i * i + 3 * i + 1;
    i := i + 1;
  }
  result := 1;
  return;
}
