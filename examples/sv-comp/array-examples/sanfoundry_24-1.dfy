// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sanfoundry_24-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/sanfoundry_24-1.yml (expected: safe), translated from the C program by
// hand: the even and the odd elements of an arbitrary array are printed by procedures that assert their parity
// (inlined)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the assertions repeat the tests

method main() {
  var i: int;
  var num: int;
  var v: int;
  var array: array<int, int>;
  num := *;
  i := 0;
  while i < num {
    v := *;
    array := array[i := v];
    i := i + 1;
  }
  i := 0;
  while i < num {
    if array[i] % 2 == 0 {
      assert array[i] % 2 == 0;
    }
    i := i + 1;
  }
  i := 0;
  while i < num {
    if array[i] % 2 != 0 {
      assert array[i] % 2 != 0;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
