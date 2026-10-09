// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/sina1.dfy
// SV-COMP array-fpi/sina1.yml (expected: safe), translated from the C program by hand: sum
// counts to N, and a is set to sum, which is N; sum[0] of the one-element array as a scalar
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var N: int;
  var a: array<int, int>;
  var sum: int;
  var i: int;
  N := *;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    sum := sum + 1;
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
