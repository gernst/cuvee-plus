// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/indp2f.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/indp2f.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of indp2 with other constants or assertions; checks a[i]==0

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
      a := a[i := (i - 1) * (i + 1)];
      i := i + 1;
    }
    i := 0;
    while i < N {
      a := a[i := a[i] - i * i];
      i := i + 1;
    }
    i := 0;
    while i < N {
      a := a[i := a[i] - 1];
      i := i + 1;
    }
    i := 0;
    while i < N {
      assert a[i] == 0;
      i := i + 1;
    }
    result := 1;
    return;
  }
}
