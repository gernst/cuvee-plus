// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/dafny/loop-invariants/linear-inequality-inv-a.dfy
// SV-COMP loop-invariants/linear-inequality-inv-a.yml (expected: safe), translated from the C
// program by hand: the sum s of n <= 255 values v <= 255 (unsigned char, as int with bounds) is at least the last
// value and at most 255 * 255
//
// findings: the bounds of the chosen values are iteration constraints, abstracted by the predicates below_prefix and
// nonneg_prefix of teq.dfy; the last value of the trace that takes them
// is earlier(n - 1, xs) by a lemma; the sum is bounded by n * b and by each value, by the lemmas of teq.dfy; -split splits the hypothesis n == 0 || n == N of the number of iterations; closed (no output)

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
    s := s + v;
    i := i + 1;
  }
  assert s >= v;
  assert s <= M * M;
}

// remaining goals of -teq -simplify -split -simplify:
// none
