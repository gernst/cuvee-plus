// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/ifcompf.dfy
// SV-COMP array-fpi/ifcompf.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ifcomp with other constants or assertions; checks c[i] == i*i*i

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var i: int, a: array<int, int>, b: array<int, int>, c: array<int, int>;
  N := *;
  if N <= 0 {
    result := 1;
    return;
  }
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := 0];
    } else {
      a := a[i := a[i - 1] + 6];
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
    if i == 0 {
      c := c[0 := 0];
    } else {
      c := c[i := c[i - 1] + b[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert c[i] == i * i * i;
    i := i + 1;
  }
  result := 1;
  return;
}
