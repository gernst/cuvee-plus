// ./Cuvee.sh -teq -simplify examples/sv-comp/array-programs/partial_mod_count_1.dfy
// SV-COMP array-programs/partial_mod_count_1.yml (expected: safe), translated from the C program by hand:
// a[i] = i + 1, overwritten by i % R for i > N / 2 with R = 1, and the count j of zeros is checked to stay
// below N / 2 (unsigned R is int)
//
// findings: the stores split on k > N / 2, joined into a store of a conditional value by a lemma generic in the
// condition, after which teq.dfy summarizes them as stores over the map of the conditional; open: the count j of
// zeros is count(0, selects(a, ⌊counter(0, 1, n)⌋)), which needs the reads of the stores as a prefix of the map,
// and the count over a map split at the threshold N / 2 into the counts below and above it, where the side
// conditions n <= N / 2 or N / 2 < n follow only from the conclusion, a[n] == 0, while j is defined in the
// hypotheses, which are simplified without that case (partial_mod_count_3 to _5 are variants)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function prefix<a>(k: int, xs: seq<a>): seq<a>
function count<a>(x: a, xs: seq<a>): int

// a store at the iteration k whose value depends on a case split on k is a store of the conditional value (with a
// further dependency ys)
lemma {:rw} {:teq} trace_1(a0: array<int, int>, n: int, ys: seq<int>, C: (int) -> bool, F: (int) -> int,
                           G: (int) -> int)
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: case C(k) => a[k := F(k)] case !C(k) => a[k := G(k)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[k := if C(k) then F(k) else G(k)])

method main() {
  var N: int;
  var i: int;
  var j: int;
  var R: int;
  var a: array<int, int>;
  assume 0 < N;
  j := 0;
  R := 1;
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
    assert j < N / 2;
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
//                                                        then 0
//                                                        else k + 1))
//       && K₁₉ == counter(0, 1, n₁₇)
//       && j₂₂ == count(0, selects(a₁₃, ⌊I₂₁⌋))
//       && J₂₀ == counts(0, 0, selects(a₁₃, ⌊I₂₁⌋))
//       && I₂₁ == counter(0, 1, n₁₇)
//       && invs(for ⌊K₁₉⌋, ⌊J₂₀⌋, ⌊I₂₁⌋
//               check k₁₈, j₁₅, i₁₆ ::
//                 (if 500000 < k₁₈ then 0 else k₁₈ + 1) == 0 && j₁₅ < 499999
//                   || (if 500000 < k₁₈ then 0 else k₁₈ + 1) != 0 && j₁₅ < 500000)
//       && 0 <= n₁₇ < 1000000
//       ==> ((if 500000 < n₁₇ then 0 else n₁₇ + 1) == 0 ==> j₂₂ < 499999)
//         && ((if 500000 < n₁₇ then 0 else n₁₇ + 1) != 0 ==> j₂₂ < 500000)
