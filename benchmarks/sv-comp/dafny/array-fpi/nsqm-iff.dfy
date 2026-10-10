// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/nsqm-iff.dfy
// SV-COMP array-fpi/nsqm-iff.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nsqm-if with other constants or assertions; checks a[i] == (i+1)*(i+1)

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
  i := 0;
  while i < N {
    if i == 0 {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + 2];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := N + 1];
    } else {
      a := a[i := a[i - 1] + b[i - 1] + 2];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == (i + 1) * (i + 1);
    i := i + 1;
  }
  result := 1;
  return;
}
