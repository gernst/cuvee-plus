// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/sina2.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/sina2.yml (expected: safe), translated from the C program by hand: a is set
// to 1, sum is N, and sum is added to each element, which is N + 1 then; sum[0] of the one-element array as a
// scalar
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

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
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N + 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
