// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-invariants64/linear-inequality-inv-d.dfy
// SV-COMP loop-invariants64/linear-inequality-inv-d.yml (expected: safe), translated from the C
// program by hand: as loop-invariants/linear-inequality-inv-a for unsigned int, 0 < n <= 2^32 - 1 values v <= 2^32
// - 1, whose sum (unsigned long) is at most (2^32 - 1)^2
//
// findings: with the lemmas of loop-invariants/linear-inequality-inv-a and -split; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing; the lemmas
// are those of loop-invariants/linear-inequality-inv-a
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
  assume 0 < n <= 4294967295;
  v := 0;
  s := 0;
  i := 0;
  while i < n {
    v := *;
    assume 0 <= v <= 4294967295;
    s := s + v;
    i := i + 1;
  }
  assert s >= v;
  assert s <= 18446744065119617025;
}

// remaining goals of -teq -simplify -split -simplify:
// none
