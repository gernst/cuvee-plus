// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/loop-invariants/linear-inequality-inv-b.dfy
// SV-COMP loop-invariants/linear-inequality-inv-b.yml (expected: unsafe), translated from the C
// program by hand: as linear-inequality-inv-a, but the sum is an unsigned char, which wraps around modulo 256, such
// that it can be below the last value
//
// findings: unsafe: the sum is an unsigned char and wraps around, modeled by % 256; open, as expected, with the
// lemma current_1 of linear-inequality-inv-a, and below_prefix and nonneg_prefix of teq.dfy

// are those of loop-invariants/linear-inequality-inv-a

// the iteration constraints of values chosen between 0 and b in each of n iterations (with a further dependency hs),
// abstracted by the predicates below_prefix and nonneg_prefix of teq.dfy, one lemma each, since a conjunction as a
// left-hand side does not match two conjuncts among others; below first, since the other matches x <= b as 0 <= b - x
lemma {:rw} {:teq} invs_1(n: Nat, b: int, hs: List<int>, xs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: x <= b) <==> below_prefix(n, xs, b)
lemma {:rw} {:teq} invs_2(n: Nat, hs: List<int>, xs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: 0 <= x) <==> nonneg_prefix(n, xs)

// the last value of a trace that takes the values xs, and its initial value x0 if there are none
lemma {:rw} {:teq} current_1(x0: int, n: Nat, xs: List<int>)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, xs do v, k, x :: x)) == if n == zero then x0 else earlier(natural(integer(n) - 1), xs)

method main() {
  var M: int;
  var n: int;
  var v: int;
  var s: int;
  var i: int;
  n := *;
  assume 0 <= M;
  assume 0 <= n <= M;
  v := 0;
  s := 0;
  i := 0;
  while i < n {
    v := *;
    assume 0 <= v <= M;
    s := rem(s + v, 256);
    i := i + 1;
  }
  assert s >= v;
  assert s <= M * M;
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall n₅: int, v₁₇: int, s₁₈: int, K₁₃: Trace<int>, S₁₅: Trace<int>,
//          V?₁₀: seq<int> ::
//     n₅ <= 255
//       && K₁₃ == counter(0, 1, n₅)
//       && v₁₇ == earlier(n₅ + -1, V?₁₀)
//       && s₁₈ == current(S₁₅)
//       && S₁₅ == trace(0, for ⌊K₁₃⌋, V?₁₀ do s₇, k₁₂, v₉ :: (s₇ + v₉) % 256)
//       && 0 < n₅
//       && nonneg(n₅, V?₁₀)
//       && below(n₅, V?₁₀, 255)
//       ==> v₁₇ <= s₁₈
// goal
//   forall n₅: int, s₁₈: int, K₁₃: Trace<int>, S₁₅: Trace<int>, V?₁₀: seq<int> ::
//     n₅ <= 255
//       && K₁₃ == counter(0, 1, n₅)
//       && s₁₈ == current(S₁₅)
//       && S₁₅ == trace(0, for ⌊K₁₃⌋, V?₁₀ do s₇, k₁₂, v₉ :: (s₇ + v₉) % 256)
//       && 0 < n₅
//       && nonneg(n₅, V?₁₀)
//       && below(n₅, V?₁₀, 255)
//       ==> s₁₈ <= 65025
// goal
//   forall s₁₈: int, K₁₃: Trace<int>, S₁₅: Trace<int>, V?₁₀: seq<int> ::
//     K₁₃ == counter(0, 1, 0)
//       && s₁₈ == current(S₁₅)
//       && S₁₅ == trace(0, for ⌊K₁₃⌋, V?₁₀ do s₇, k₁₂, v₉ :: (s₇ + v₉) % 256)
//       && nonneg(0, V?₁₀)
//       && below(0, V?₁₀, 255)
//       ==> 0 <= s₁₈
// goal
//   forall s₁₈: int, K₁₃: Trace<int>, S₁₅: Trace<int>, V?₁₀: seq<int> ::
//     K₁₃ == counter(0, 1, 0)
//       && s₁₈ == current(S₁₅)
//       && S₁₅ == trace(0, for ⌊K₁₃⌋, V?₁₀ do s₇, k₁₂, v₉ :: (s₇ + v₉) % 256)
//       && nonneg(0, V?₁₀)
//       && below(0, V?₁₀, 255)
//       ==> s₁₈ <= 65025
