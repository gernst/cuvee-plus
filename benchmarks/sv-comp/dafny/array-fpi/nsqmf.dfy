// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/array-fpi/nsqmf.dfy
// SV-COMP array-fpi/nsqmf.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of nsqm, whose first element is 1 instead of N + 1
//
// findings: unsafe, not closed with the lemmas of nsqm, as expected
// note: 3 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  N := *;
  assume 0 < N;
  b := b[0 := 1];
  a := a[0 := 1];
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + 2];
    i := i + 1;
  }
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + b[i - 1] + 2];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N + (i + 1) * (i + 1);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// goal forall K₂₇: Trace<int> :: !(K₂₇ == counter(0, 1, 0) && |⌊K₂₇⌋| == 0)
// goal
//   forall n₈: int, n₂₅: int, K₂₇: Trace<int> ::
//     !(n₈ <= 536870910
//         && 0 < n₈
//         && K₂₇ == counter(0, 1, n₂₅)
//         && |⌊K₂₇⌋| == 0 <= n₂₅ <= n₈)
