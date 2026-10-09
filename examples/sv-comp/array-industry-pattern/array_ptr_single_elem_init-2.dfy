// ./Cuvee.sh -teq -simplify examples/sv-comp/array-industry-pattern/array_ptr_single_elem_init-2.dfy
// SV-COMP ReachSafety-Arrays/array-industry-pattern/array_ptr_single_elem_init-2.yml (expected: unsafe), translated from the C program by hand:
// as array_single_elem_init, but a[15000] != 1 is checked after a[15000] = 1
//
// findings: unsafe: a[15000] is 1 when checked; -teq -simplify reduces the goal to false, i.e., finds the violation

method main() {
  var i: int;
  var q: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  i := 0;
  while i < 100000 {
    havoc q;
    a := a[i := 0];
    if q == 0 {
      a := a[i := 1];
      b := b[i := i % 2];
    }
    if a[i] != 0 {
      if b[i] == 0 {
        c := c[i := 0];
      } else {
        c := c[i := 1];
      }
    }
    i := i + 1;
  }
  a := a[15000 := 1];
  i := 0;
  while i < 100000 {
    if i == 15000 {
      assert a[i] != 1;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal false
