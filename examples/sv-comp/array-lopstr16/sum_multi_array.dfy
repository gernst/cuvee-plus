// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/sum_multi_array.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/sum_multi_array.yml (expected: safe), translated from the C program by hand:
// a[i] and b[i] are arbitrary, c[i] = a[i] + b[i], which is checked (the fields n of structs are the arrays)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var v: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  i := 0;
  while i < 1000000 {
    havoc v;
    a := a[i := v];
    havoc v;
    b := b[i := v];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    assert c[i] == a[i] + b[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
