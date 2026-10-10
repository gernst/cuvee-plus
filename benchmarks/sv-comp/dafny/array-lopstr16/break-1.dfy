// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-lopstr16/break-1.dfy
// SV-COMP array-lopstr16/break-1.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; the fields of structs are arrays of their own; the pointers are allocated unless c > 5,
// which leaves the loop at once, and they are checked to be allocated if c <= 5
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var c: int;
  var s: array<int, bool>;
  assume 0 < N;
  c := *;
  i := 0;
  while i < N {
    if c > 5 {
      break;
    }
    s := s[i := true];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if c <= 5 {
      assert s[i];
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
