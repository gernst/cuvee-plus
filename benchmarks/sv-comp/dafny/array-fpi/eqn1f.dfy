// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/eqn1f.dfy
// SV-COMP array-fpi/eqn1f.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of eqn1, where a increases by 20, such that b is not i * i + i + 1
//
// findings: unsafe, not closed with the lemmas of eqn1, as expected: b[i] is 10 * i * i - 8 * i + 1 then, which
// differs from i * i + i + 1
// note: 2 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  N := *;
  assume 0 < N;
  a := a[0 := 2];
  b := b[0 := 1];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 20];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == i * i + i + 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall N₅: int, n₈: int, n₁₇: int, n₂₅: int, K₂₇: Trace<int>,
//          I₂₈: Trace<int> ::
//     N₅ <= 536870911
//       && (n₈ == 0 || 1 < N₅ && n₈ < N₅)
//       && N₅ <= n₈ + 1
//       && (n₁₇ == 0 || 1 < N₅ && n₁₇ < N₅)
//       && N₅ <= n₁₇ + 1
//       && K₂₇ == counter(0, 1, n₂₅)
//       && I₂₈ == counter(0, 1, n₂₅)
//       && invs(for ⌊K₂₇⌋, ⌊I₂₈⌋
//               check k₂₆, i₂₄ ::
//                 (-16 * k₂₆ + 20 * k₂₆ * k₂₆) / 2 == k₂₆ + k₂₆ * k₂₆)
//       && 0 <= n₂₅ < N₅
//       ==> (-16 * n₂₅ + 20 * n₂₅ * n₂₅) / 2 == n₂₅ + n₂₅ * n₂₅
