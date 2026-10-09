// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/eqn2f.dfy
// SV-COMP array-fpi/eqn2f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of eqn2 with other constants or assertions; checks b[i] == 2*i*i + 2*i + 1

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
  assume N <= 536870911;
  a := a[0 := 8];
  b := b[0 := 1];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 4];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == 2 * i * i + 2 * i + 1;
    i := i + 1;
  }
  result := 1;
  return;
}
