// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_init_pair_symmetr.dfy
// SV-COMP ReachSafety-Arrays/array-cav19/array_init_pair_symmetr.yml (expected: safe), translated from the C program by hand:
// a[i] = x and b[i] = -x for a value x chosen in each iteration, c[i] = a[i] + b[i], and c[i] == 0 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): a[i] + b[i] is x + -x

method main() {
  var N: int;
  var i: int;
  var x: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  N := 100000;
  i := 0;
  while i < N {
    havoc x;
    assume x > -100000 && x < 100000;
    a := a[i := x];
    b := b[i := -x];
    i := i + 1;
  }
  i := 0;
  while i < N {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
  i := 1;
  while i < N {
    assert c[i] == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
