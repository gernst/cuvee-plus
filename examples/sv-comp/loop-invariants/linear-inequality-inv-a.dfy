// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-invariants/linear-inequality-inv-a.dfy
// SV-COMP loop-invariants/linear-inequality-inv-a.yml (expected: safe), translated from the C
// program by hand: the sum s of n <= 255 values v <= 255 (unsigned char, as int with bounds) is at least the last
// value and at most 255 * 255
//
// findings: the bounds of the chosen values are iteration constraints, abstracted by the predicates below and
// nonneg, below first, since nonneg would match x <= b as 0 <= b - x; the last value of the trace that takes them
// is earlier(n - 1, xs) by a lemma; the sum is bounded by n * b and by each value, by lemmas whose left-hand sides
// are comparisons; -split splits the hypothesis n == 0 || n == N of the number of iterations; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀
function sum(values: seq<int>): int

// the n values xs, one per iteration, are nonnegative, and at most b, auxiliary predicates, which are not defined
predicate nonneg(n: int, xs: seq<int>)
predicate below(n: int, xs: seq<int>, b: int)

// the iteration constraints of values chosen between 0 and b in each of n iterations (with a further dependency hs),
// abstracted by the predicates nonneg and below, one lemma each, since a conjunction as a left-hand side does not
// match two conjuncts among others; below comes first, since nonneg matches x <= b as 0 <= b - x otherwise
lemma {:rw} {:teq} invs_1(n: int, b: int, hs: seq<int>, xs: seq<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: x <= b) <==> below(n, xs, b)
lemma {:rw} {:teq} invs_2(n: int, hs: seq<int>, xs: seq<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: 0 <= x) <==> nonneg(n, xs)

// the last value of a trace that takes the values xs, and its initial value x0 if there are none
lemma {:rw} {:teq} current_1(x0: int, n: int, xs: seq<int>)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, xs do v, k, x :: x)) == if 0 < n then earlier(n - 1, xs) else x0

// the sum of n values that are at most b is at most n * b, and that of nonnegative ones at least each of them; the left-hand sides are
// comparisons
lemma {:rw} {:teq} sum_1(n: int, xs: seq<int>, b: int, c: int)
  requires below(n, xs, b) && n * b <= c
  ensures sum(xs) <= c
lemma {:rw} {:teq} earlier_1(n: int, xs: seq<int>, b: int, j: int)
  requires nonneg(n, xs) && 0 <= j < n
  ensures earlier(j, xs) <= sum(xs)

lemma {:rw} {:teq} sum_2(n: int, xs: seq<int>)
  requires nonneg(n, xs)
  ensures 0 <= sum(xs)

method main() {
  var n: int;
  var v: int;
  var s: int;
  var i: int;
  n := *;
  assume 0 <= n <= 255;
  v := 0;
  s := 0;
  i := 0;
  while i < n {
    v := *;
    assume 0 <= v <= 255;
    s := s + v;
    i := i + 1;
  }
  assert s >= v;
  assert s <= 65025;
}

// remaining goals of -teq -simplify -split -simplify:
// none
