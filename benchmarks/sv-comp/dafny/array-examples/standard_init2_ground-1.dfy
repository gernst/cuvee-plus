// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_init2_ground-1.dfy
// SV-COMP array-examples/standard_init2_ground-1.yml (expected: unsafe), translated from the C program by hand:
// as standard_init2_ground-2, but the array is checked to be 42, which the second loop overwrote (the -1
// variants of standard_init3 to _init9 are similar)
//
// findings: unsafe: the second loop overwrote 42 with 43; open, as expected, where the remaining atom compares 43
// with 42 at the instantiated position
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 43];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a[x] == 42;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₂₃: int, K₂₅: Trace<int> ::
//     !(K₂₅ == counter(0, 1, n₂₃) && |⌊K₂₅⌋| == 0 <= n₂₃ < 100000)
