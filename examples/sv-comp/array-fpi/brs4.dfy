// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/brs4.dfy
// SV-COMP array-fpi/brs4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of brs1 with other constants or assertions; checks sum[0] <= 4*N

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

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
  assume N <= 536870911;
  i := 0;
  while i < N {
    if (remainder(i, 4)) == 0 {
      a := a[i := 4];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      sum := sum[0 := 0];
    } else {
      sum := sum[0 := sum[0] + a[i]];
    }
    i := i + 1;
  }
  assert sum[0] <= 4 * N;
  result := 1;
  return;
}
