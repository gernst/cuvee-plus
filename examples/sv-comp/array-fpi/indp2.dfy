// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/indp2.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/indp2.yml (expected: safe), translated from the C program by hand: a[i] is
// set to (i - 1) * (i + 1), then i * i is subtracted and 1 added, which gives 0
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the three updates at the same
// positions compose to (i - 1) * (i + 1) - i * i + 1, which the polynomials normalize to 0

method main() {
  var N: int;
  var a: array<int, int>;
  var i: int;
  N := *;
  assume 0 < N <= 536870911;
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
    a := a[i := a[i] + 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
