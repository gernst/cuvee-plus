// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/s1if.dfy
// SV-COMP array-fpi/s1if.yml (expected: safe), translated from the C program by hand: a of
// arbitrary size N is set to 1, and the elements that are 1 are summed (the others would multiply), which gives N;
// sum[0] of the one-element array as a scalar
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the reads of the constant 1
// decide the guard, and the sum of the constants is N

method main() {
  var N: int;
  var a: array<int, int>;
  var sum: int;
  var i: int;
  N := *;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 1 {
      sum := sum + a[i];
    } else {
      sum := sum * a[i];
    }
    i := i + 1;
  }
  assert sum == N;
}

// remaining goals of -teq -simplify:
// none
