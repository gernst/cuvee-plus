// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/res2.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/res2.yml (expected: safe), translated from the C program by hand: three
// arrays of ones are summed up, which gives at most 3 N (res2o is a variant)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
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
    b := b[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + b[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    c := c[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + c[i];
    i := i + 1;
  }
  assert sum <= 3 * N;
}

// remaining goals of -teq -simplify:
// none
