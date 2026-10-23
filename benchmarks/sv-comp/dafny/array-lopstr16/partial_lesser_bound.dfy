// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-lopstr16/partial_lesser_bound.dfy
// SV-COMP array-lopstr16/partial_lesser_bound.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; the fields of structs are arrays of their own; the array of pointers is set to null,
// then the first half is allocated, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var a: array<int, bool>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := false];
    i := i + 1;
  }
  i := 0;
  while i < quot(N, 2) {
    a := a[i := true];
    i := i + 1;
  }
  i := 0;
  while i < quot(N, 2) {
    assert a[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
