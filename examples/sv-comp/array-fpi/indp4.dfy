// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/indp4.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/indp4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of indp1f with other constants or assertions; checks a[i]==i*i+1

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
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
      assert a[i] == i * i + 1;
      i := i + 1;
    }
    result := 1;
    return;
  }
}
