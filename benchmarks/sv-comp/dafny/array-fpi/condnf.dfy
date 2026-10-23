// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/dafny/array-fpi/condnf.dfy
// SV-COMP array-fpi/condnf.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of condn, which keeps the elements above N and caps the others
//
// findings: unsafe, not closed with the lemma of condn, as expected: the guard is not the clamp of the lemma
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var tmp: int;
  N := *;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] > N {
      a := a[i := a[i]];
    } else {
      a := a[i := N];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] <= N;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall a₃: array<int, int>, N₅: int, a₁₈: array<int, int>,
//          A₁₅: Trace<array<int, int>>, I₁₆: Trace<int>, Tmp?₁₀: seq<int>,
//          a₂₈: array<int, int>, K₂₅: Trace<int>, A₂₆: Trace<array<int, int>>,
//          I₂₇: Trace<int>, n₃₁: int, K₃₃: Trace<int>, I₃₄: Trace<int> ::
//     N₅ <= 536870911
//       && a₁₈ == current(A₁₅)
//       && A₁₅ == stores(a₃, ⌊I₁₆⌋, Tmp?₁₀)
//       && I₁₆ == counter(0, 1, N₅)
//       && K₂₅ == counter(0, 1, N₅)
//       && a₂₈ == current(A₂₆)
//       && A₂₆
//         == trace(a₁₈, for ⌊K₂₅⌋, ⌊I₂₇⌋
//                       do a₂₁, k₂₄, i₂₂ ::
//                         case N₅ < a₂₁[k₂₄] => a₂₁
//                         case a₂₁[k₂₄] <= N₅ => a₂₁[k₂₄ := N₅])
//       && I₂₇ == counter(0, 1, N₅)
//       && K₃₃ == counter(0, 1, n₃₁)
//       && I₃₄ == counter(0, 1, n₃₁)
//       && invs(for ⌊K₃₃⌋, ⌊I₃₄⌋ check k₃₂, i₃₀ :: a₂₈[k₃₂] <= N₅)
//       && 0 <= n₃₁ < N₅
//       ==> a₂₈[n₃₁] <= N₅
