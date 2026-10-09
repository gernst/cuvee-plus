// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/condmf.dfy
// SV-COMP array-fpi/condmf.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of condm with other constants or assertions; checks a[i] % 2 == N % 2

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var i: int, a: array<int, int>;
  N := *;
  if N <= 0 {
    result := 1;
    return;
  }
  assume N <= 536870911;
  i := 0;
  while i < N {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if (remainder(N, 2)) == 1 {
      a := a[i := a[i] + 2];
    } else {
      a := a[i := a[i] + 1];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert (remainder(a[i], 2)) == (remainder(N, 2));
    i := i + 1;
  }
  result := 1;
  return;
}
