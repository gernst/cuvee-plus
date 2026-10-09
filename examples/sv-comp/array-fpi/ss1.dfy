// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ss1.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ss1.yml (expected: safe), translated from the C program by hand: a is set to
// 1, sum is N, sum is added to each element, which is N + 1 then, and sum adds the elements to N, which gives N *
// (N + 2); sum[0] of the one-element array as a scalar
//
// findings: the elements of stores at the positions of a counter, read back at the positions of an equal counter,
// are the stored values, which a lemma states with both counters as patterns, since they are different trace
// variables in the program; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

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
    sum := sum + a[i];
    i := i + 1;
  }
  assert sum == N * (N + 2);
}

// remaining goals of -teq -simplify:
// none
