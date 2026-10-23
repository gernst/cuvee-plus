// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/s2if.dfy
// SV-COMP array-fpi/s2if.yml (expected: safe), translated from the C program by hand: a is set
// to 2, and the elements that are 2 are summed (the others would multiply), which gives 2 * N; sum[0] of the
// one-element array as a scalar
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  N := *;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 2];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 2 {
      sum := sum + a[i];
    } else {
      sum := sum * a[i];
    }
    i := i + 1;
  }
  assert sum == 2 * N;
}

// remaining goals of -teq -simplify:
// none
