// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-cav19/array_init_pair_sum_const.dfy
// SV-COMP array-cav19/array_init_pair_sum_const.yml (expected: safe), translated from the C
// program by hand: a[i] = 1, b[i] = 2, c[i] = a[i] + b[i], and c[i] >= 3 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var i: int;
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  N := *;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 1];
    b := b[i := 2];
    i := i + 1;
  }
  i := 0;
  while i < N {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
  i := 1;
  while i < N {
    assert c[i] >= 3;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
