// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/modnf.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/modnf.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of modn, which asserts that the elements, which are 0, are 1
//
// findings: unsafe, not closed with the lemma of modn, as expected: the elements are 0
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var a: array<int, int>;
  var sum: int;
  var i: int;
  havoc N;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    sum := sum + 1;
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := sum % N];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall N₅: int, n₂₅: int, K₂₇: Trace<int> ::
//     !(N₅ <= 536870911 && K₂₇ == counter(0, 1, n₂₅) && |⌊K₂₇⌋| == 0 <= n₂₅ < N₅)
