// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-cav19/array_tiling_tcpy.dfy
// SV-COMP array-cav19/array_tiling_tcpy.yml (expected: safe), translated from the C program by hand:
// acopy is a copy of a of length 2 S, filled from both ends at once, and checked to agree with a
//
// findings: a copy from both ends, at the positions c - k and k, by a lemma generic in c; open: the lemma does not
// match the positions 2 * S + -k + -1, since a variable of a pattern in a sum with a bound variable takes a single
// summand, here not 2 * S + -1, and the variant c - 1 - k does not match either, also not S + -k + -1 (see TODO.md)

// a loop that copies b into a at the positions c - k and k in the iterations k = 0, ..., n - 1, i.e., from both ends
// at once, agrees with b at the positions below n and above c - n, up to c, and keeps the others (with a further
// dependency ys that the update does not use)
lemma {:rw} {:teq} current_1(a0: array<int, int>, b: array<int, int>, n: Nat, c: int, j: int, ys: List<int>)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[c - k := b[c - k]][k := b[k]]))[j]
    == if 0 <= j < integer(n) || c - integer(n) < j <= c then b[j] else a0[j]

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  var acopy: array<int, int>;
  S := *;
  assume S > 1;
  i := 0;
  while i < S {
    acopy := acopy[2 * S - (i + 1) := a[2 * S - (i + 1)]];
    acopy := acopy[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while i < 2 * S {
    assert acopy[i] == a[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, acopy₄: array<int, int>, S₅: int,
//          acopy₁₃: array<int, int>, K₁₀: Trace<int>,
//          Acopy₁₁: Trace<array<int, int>>, I₁₂: Trace<int>, n₁₆: int,
//          K₁₈: Trace<int>, I₁₉: Trace<int> ::
//     1 < S₅ < 1073741823
//       && K₁₀ == counter(0, 1, S₅)
//       && acopy₁₃ == current(Acopy₁₁)
//       && Acopy₁₁
//         == trace(acopy₄, for ⌊K₁₀⌋, ⌊I₁₂⌋
//                          do acopy₆, k₉, i₇ ::
//                            acopy₆[2 * S₅ + -k₉ + -1 := a₃[2 * S₅ + -k₉ + -1]][
//                              k₉ :=
//                              a₃[k₉]])
//       && I₁₂ == counter(0, 1, S₅)
//       && K₁₈ == counter(0, 1, n₁₆)
//       && I₁₉ == counter(0, 1, n₁₆)
//       && invs(for ⌊K₁₈⌋, ⌊I₁₉⌋ check k₁₇, i₁₅ :: acopy₁₃[k₁₇] == a₃[k₁₇])
//       && 0 <= n₁₆ < 2 * S₅
//       ==> acopy₁₃[n₁₆] == a₃[n₁₆]
