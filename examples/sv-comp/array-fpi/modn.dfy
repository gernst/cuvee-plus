// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/modn.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/modn.yml (expected: safe), translated from the C program by hand: sum counts
// to N, and a is set to sum % N, which is 0; sum[0] of the one-element array as a scalar
//
// findings: teq.dfy accelerates the loops, the remaining goal is N % N == 0, which a lemma of arithmetic states for
// positive N; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

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
    a := a[i := sum % N];
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
