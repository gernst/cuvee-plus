// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-lopstr16/sum_multi_array.dfy
// SV-COMP array-lopstr16/sum_multi_array.yml (expected: safe), translated from the C program by hand:
// a[i] and b[i] are arbitrary, c[i] = a[i] + b[i], which is checked (the fields n of structs are the arrays)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var v: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    v := *;
    a := a[i := v];
    v := *;
    b := b[i := v];
    i := i + 1;
  }
  i := 0;
  while i < N {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert c[i] == a[i] + b[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
