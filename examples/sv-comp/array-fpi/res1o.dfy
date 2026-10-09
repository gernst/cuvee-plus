// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/res1o.dfy
// SV-COMP array-fpi/res1o.yml (expected: safe), translated from the C program by hand: two
// arrays of ones are summed up, which gives at most 2 N
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (res2o is a variant)

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  var b: array<int, int>;
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
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := 1];
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
