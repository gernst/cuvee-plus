// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/eqn5f.dfy
// SV-COMP array-fpi/eqn5f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of eqn5 with other constants or assertions; checks b[i] == 5*i*i + 5*i + 1

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
  a := a[0 := 1];
  b := b[0 := 1];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 10];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == 5 * i * i + 5 * i + 1;
    i := i + 1;
  }
  result := 1;
  return;
}
