// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/res1.dfy
// SV-COMP array-fpi/res1.yml (expected: safe), translated from the C program by hand: a and b
// are set to 1, and sum adds both, which is at most 2 * N; sum[0] of the one-element array as a scalar
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var sum: int;
  N := *;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + b[i];
    i := i + 1;
  }
  assert sum <= 2 * N;
}

// remaining goals of -teq -simplify:
// none
