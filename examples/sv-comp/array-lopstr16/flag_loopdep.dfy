// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/flag_loopdep.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/flag_loopdep.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; the fields of structs are arrays of their own; the pointers are allocated (the function
// init, inlined), the flag is set if one is not null, and if it is not set, all are checked to be null
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var flag: int;
  var a: array<int, bool>;
  flag := 0;
  i := 0;
  while i < 1000000 {
    a := a[i := true];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    if a[i] {
      flag := 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    if flag == 0 {
      assert !a[i];
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
