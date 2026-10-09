// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_init2_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_init2_ground-1.yml (expected: unsafe), translated from the C program by hand:
// as standard_init2_ground-2, but the array is checked to be 42, which the second loop overwrote (the -1
// variants of standard_init3 to _init9 are similar)
//
// findings: unsafe: the second loop overwrote 42 with 43; open, as expected, where the remaining atom compares 43
// with 42 at the instantiated position

method main() {
  var i: int;
  var x: int;
  var a: array<int, int>;
  i := 0;
  while i < 100000 {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 43];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] == 42;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₂₃: int, K₂₅: Trace<int> ::
//     !(K₂₅ == counter(0, 1, n₂₃) && |⌊K₂₅⌋| == 0 <= n₂₃ < 100000)
