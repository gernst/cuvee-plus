// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/partial_lesser_bound.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/partial_lesser_bound.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; the fields of structs are arrays of their own; the array of pointers is set to null,
// then the first half is allocated, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var a: array<int, bool>;
  i := 0;
  while i < 1000000 {
    a := a[i := false];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 / 2 {
    a := a[i := true];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 / 2 {
    assert a[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
