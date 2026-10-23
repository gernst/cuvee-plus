// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-industry-pattern/array_ptr_single_elem_init-2.dfy
// SV-COMP array-industry-pattern/array_ptr_single_elem_init-2.yml (expected: unsafe), translated from the C program by hand:
// as array_single_elem_init, but a[15000] != 1 is checked after a[15000] = 1
//
// findings: unsafe: a[15000] is 1 when checked; -teq -simplify reduces the goal to false, i.e., finds the violation
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var q: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    q := *;
    a := a[i := 0];
    if q == 0 {
      a := a[i := 1];
      b := b[i := rem(i, 2)];
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
  while i < N {
    if i == 15000 {
      assert a[i] != 1;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal false
