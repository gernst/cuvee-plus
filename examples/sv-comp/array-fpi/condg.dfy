// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/condg.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/condg.yml (expected: safe), translated from the C program by hand: a is set
// to 1, sum is N, and each element is decreased by 1 if sum is N, which gives 0; sum[0] of the one-element array as
// a scalar
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the guard sum == N is decided by
// the closed form of the sum

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  havoc N;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if sum == N {
      a := a[i := a[i] - 1];
    } else {
      a := a[i := a[i] + 1];
    }
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
