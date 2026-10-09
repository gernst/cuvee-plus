// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_init_var_plus_ind3.dfy
// SV-COMP ReachSafety-Arrays/array-cav19/array_init_var_plus_ind3.yml (expected: safe), translated from the C program by hand:
// a[i] = j, where j accumulates -0 - 1 - ... - (i - 1), in a loop that may stop early (a nondeterministic
// break), and a[k] <= 0 is checked for 4 <= k below the exit
//
// findings: the reads of a are sums over prefixes of the map of -k, which a lemma generic in F turns into the map
// over a shorter counter; open: the remaining atom 0 <= (7 * n + n * n + 12) / 2 is (n + 3) * (n + 4) / 2, which
// the halves (x + x * x) / 2 do not match, since patterns match modulo A/C, not modulo the substitution of n + 3
// for x, and a variable as a coefficient does not match the literal 7 (see TODO.md)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function prefix<a>(k: int, xs: seq<a>): seq<a>
function sum(values: seq<int>): int

// a prefix of length m of the values F(k) of n iterations k = 0, ..., n - 1 are the values of the first m iterations
// (with a further dependency ys that F does not use)
lemma {:rw} {:free} {:teq} forall m: int, n: int, ys: seq<int>, F: (int) -> int ::
  if 0 <= m <= n
  then prefix(m, maps(for ⌊counter(0, 1, n)⌋, ys yield k, y :: F(k))) == maps(for ⌊counter(0, 1, m)⌋ yield k :: F(k))

// the sums 0 + 1 + ... + x and 0 + 1 + ... + (x - 1) are nonnegative for all integers x, also plus a nonnegative d, in
// the normal form of the simplifier (arithmetic, not about traces); the left-hand sides are comparisons
lemma {:rw} {:free} {:teq} forall x: int ::
  0 <= (x + x * x) / 2
lemma {:rw} {:free} {:teq} forall x: int ::
  0 <= (-x + x * x) / 2
lemma {:rw} {:free} {:teq} forall x: int, d: int ::
  if 0 <= d
  then 0 <= (x + x * x) / 2 + d
lemma {:rw} {:free} {:teq} forall x: int, d: int ::
  if 0 <= d
  then 0 <= (-x + x * x) / 2 + d

method main() {
  var N: int;
  var i: int;
  var j: int;
  var k: int;
  var x: int;
  var a: array<int, int>;
  N := 100000;
  j := 0;
  i := 0;
  while i < N {
    havoc x;
    if x != 0 {
      break;
    }
    a := a[i := j];
    j := j - i;
    i := i + 1;
  }
  k := 4;
  while k < i {
    assert a[k] <= 0;
    k := k + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₁₃: int, K₁₅: Trace<int>, I₁₉: Trace<int>, X?₁₂: seq<int> ::
//     K₁₅ == counter(0, 1, n₁₃)
//       && I₁₉ == counter(0, 1, n₁₃)
//       && n₁₃ < 100001
//       && invs(for ⌊K₁₅⌋, ⌊I₁₉⌋, X?₁₂ check k₁₄, i₁₀, x₁₁ :: x₁₁ == 0)
//       && 0 <= n₁₃
//       ==> (forall n₂₆: int, K₂₈: Trace<int>, K₂₉: Trace<int> ::
//              100000 == n₁₃
//                && K₂₈ == counter(0, 1, n₂₆)
//                && K₂₉ == counter(4, 1, n₂₆)
//                && invs(for ⌊K₂₈⌋, ⌊K₂₉⌋
//                        check k₂₇, k₂₅ ::
//                          0 <= (7 * k₂₇ + k₂₇ * k₂₇ + 12) / 2)
//                && 0 <= n₂₆ < 99996
//                ==> 0 <= (7 * n₂₆ + n₂₆ * n₂₆ + 12) / 2)
//         && (forall x₂₄: int, n₃₂: int, K₃₄: Trace<int>, K₃₅: Trace<int> ::
//               n₁₃ < 100000
//                 && x₂₄ != 0
//                 && K₃₄ == counter(0, 1, n₃₂)
//                 && K₃₅ == counter(4, 1, n₃₂)
//                 && invs(for ⌊K₃₄⌋, ⌊K₃₅⌋
//                         check k₃₃, k₃₁ ::
//                           0 <= (7 * k₃₃ + k₃₃ * k₃₃ + 12) / 2)
//                 && 0 <= n₃₂
//                 && n₃₂ + 4 < n₁₃
//                 ==> 0 <= (7 * n₃₂ + n₃₂ * n₃₂ + 12) / 2)
