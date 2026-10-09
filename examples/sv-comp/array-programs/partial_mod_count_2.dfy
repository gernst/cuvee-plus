// ./Cuvee.sh -teq -simplify examples/sv-comp/array-programs/partial_mod_count_2.dfy
// SV-COMP ReachSafety-Arrays/array-programs/partial_mod_count_2.yml (expected: safe), translated from the C program by hand:
// as partial_mod_count_1 with R = 2, where the count of zeros, the even i > N / 2, stays below N / 4
//
// findings: as partial_mod_count_1 with R = 2, whose count of zeros additionally counts the even positions above N
// / 2 (see the counting of remainders in loops-crafted-1/sumt2.dfy); open for the same reasons
// (partial_mod_count_limited_1 to _5, _base, and _gen are variants with a limit on the number of zeros)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function prefix<a>(k: int, xs: seq<a>): seq<a>
function count<a>(x: a, xs: seq<a>): int

// a store at the iteration k whose value depends on a case split on k is a store of the conditional value (with a
// further dependency ys)
lemma {:rw} {:free} {:teq} forall a0: array<int, int>, n: int, ys: seq<int>,
                           C: (int) -> bool, F: (int) -> int, G: (int) -> int ::
  trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: case C(k) => a[k := F(k)] case !C(k) => a[k := G(k)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[k := if C(k) then F(k) else G(k)])

method main() {
  var N: int;
  var i: int;
  var j: int;
  var R: int;
  var a: array<int, int>;
  assume 0 < N;
  j := 0;
  R := 2;
  i := 0;
  while i < N {
    a := a[i := i + 1];
    if i > N / 2 {
      a := a[i := i % R];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 0 {
      j := j + 1;
    }
    assert j < N / 4;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₅: array<int, int>, a₁₃: array<int, int>, A₁₁: Trace<array<int, int>>,
//          j₂₂: int, n₁₇: int, K₁₉: Trace<int>, J₂₀: Trace<int>,
//          I₂₁: Trace<int> ::
//     a₁₃ == current(A₁₁)
//       && A₁₁
//         == stores(a₅, ⌊counter(0, 1, 1000000)⌋, maps(for ⌊counter(0, 1,
//                                                                   1000000)⌋
//                                                      yield k ::
//                                                        if 500000 < k
//                                                        then k % 2
//                                                        else k + 1))
//       && K₁₉ == counter(0, 1, n₁₇)
//       && j₂₂ == count(0, selects(a₁₃, ⌊I₂₁⌋))
//       && J₂₀ == counts(0, 0, selects(a₁₃, ⌊I₂₁⌋))
//       && I₂₁ == counter(0, 1, n₁₇)
//       && invs(for ⌊K₁₉⌋, ⌊J₂₀⌋, ⌊I₂₁⌋
//               check k₁₈, j₁₅, i₁₆ ::
//                 (if 500000 < k₁₈ then k₁₈ % 2 else k₁₈ + 1) == 0 && j₁₅ < 249999
//                   || (if 500000 < k₁₈ then k₁₈ % 2 else k₁₈ + 1) != 0
//                     && j₁₅ < 250000)
//       && 0 <= n₁₇ < 1000000
//       ==> ((if 500000 < n₁₇ then n₁₇ % 2 else n₁₇ + 1) == 0 ==> j₂₂ < 249999)
//         && ((if 500000 < n₁₇ then n₁₇ % 2 else n₁₇ + 1) != 0 ==> j₂₂ < 250000)
