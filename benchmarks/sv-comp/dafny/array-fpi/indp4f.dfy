// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/indp4f.dfy
// SV-COMP array-fpi/indp4f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of indp4 with other constants or assertions; checks a[i]==i*i

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
  i := 0;
  while i < N {
    a := a[i := (i + 1) * (i + 1)];
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
    assert a[i] == i * i;
    i := i + 1;
  }
  result := 1;
  return;
}
