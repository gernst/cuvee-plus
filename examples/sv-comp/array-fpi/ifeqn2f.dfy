// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ifeqn2f.dfy
// SV-COMP array-fpi/ifeqn2f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ifeqn2 with other constants or assertions; checks b[i] == 2*i*i + 2*i

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
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := 4];
    } else {
      a := a[i := a[i - 1] + 4];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + a[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == 2 * i * i + 2 * i;
    i := i + 1;
  }
  result := 1;
  return;
}
