// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/dafny/loop-new/count_by_k.dfy
// SV-COMP loop-new/count_by_k.yml (expected: safe), translated from the C program by hand: i
// counts by k, between 0 and 10, up to 1000000 * k, which it hits exactly, also for k == 0, when the loop does not
// run
//
// findings: i is counter(0, k, n) with the step k, an arbitrary number between 0 and 10, whose iteration constraint
// k * j < 1000000 * k and exit are nonlinear in k; a lemma that cancels the nonnegative factor k, (k * a < k * b)
// <==> (0 < k && a < b), does not match, since the coefficient 1000000 of the monomial 1000000 * k is not matched
// by a variable of the pattern (see TODO.md); the lemma is kept
// note: 1 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var k: int;
  assume 0 < N;
  k := *;
  assume 0 <= k <= 10;
  i := 0;
  while i < N * k {
    i := i + k;
  }
  assert i == N * k;
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall k₃: int, n₅: int, K₇: Trace<int>, I₈: Trace<int> ::
//     !(0 <= k₃ <= 10
//         && K₇ == counter(0, 1, n₅)
//         && I₈ == counter(0, k₃, n₅)
//         && invs(for ⌊K₇⌋, ⌊I₈⌋ check k₆, i₄ :: k₃ * k₆ < 1000000 * k₃)
//         && 0 <= n₅
//         && 1000000 * k₃ < k₃ * n₅)
