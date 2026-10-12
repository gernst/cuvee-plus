// ./Cuvee.sh -teq -entry main -simplify examples/dafny/algorithms/selection_sort.dfy
// selection sort with nested loops: the inner loop finds the position m of the minimum of b[i..n), which is swapped
// to position i
//
// status: verified with -teq -simplify, both sorted(b, 0, n) and perm(b, a);
// the trace equation system has the outer array trace
// B == trace(a, for ⌊K⌋, ⌊I⌋, M? do b, k, i, m :: b[k := b[m]][m := b[k]]), a trace of swaps of k with the result m
// of the inner loop, and the inner loop as fragments of the iteration constraint of the outer loop, among them
// M == trace(k, for ⌊J⌋ do m, j :: case b[j] < b[m] => j case b[m] <= b[j] => m), the position of the minimum, and
// J == sums(k + 1, maps(for ⌊K'⌋ yield 1)), which the generic fragment lemmas of fragments.dfy rewrite to
// J == counter(k + 1, 1, nn) and j == integer(nn) + k + 1; the summary lemma current_selection_swaps takes these
// fragments as side conditions, matched against the facts (as current_results_bubble in bubble_sort.dfy), and
// rewrites the outer trace into a trace of swaps of k with argmin(b, k, n), the position of the minimum of b[k..n),
// an abstract function; the inner iteration constraint j < n is kept as a side condition rather than rewritten, since
// its rewritten form k + 1 + integer(nn) <= n is matched by above_iterations_def of teq.dfy with the bound
// synthesized as a map (and bound twice, since a closed side condition is decided, not matched, see NOTES.md);
// sorted(b, 0, n) then follows from sorted_prefix_steps, a generic induction over a trace of steps F that extend a
// sorted prefix partitioned from the rest, whose quantified side condition the simplifier decides by the two step
// lemmas on the swap with argmin, and perm(b, a) from perm_swaps_one

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the inner counter: a variable increased by c over the inner counter K, which is counter(0, 1, nn) in the same
// iteration, is a counter from its initial value X(k) (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the final value of an inner counter (fragments.dfy)
lemma {:rw} invs_current_counter(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: int -> int, c: int)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, Ns, js check k, nn, j :: j == X(k) + integer(nn) * c)

// the position of the minimum of b[lo..hi), lo if the range is empty
function argmin(b: array<int, int>, lo: int, hi: int): int

// the summary of the inner loop: in iteration k, the inner loop selects the position m of the minimum of b[k..n),
// given its trace equations and iteration constraint as side conditions: m is the current value of a selection
// trace M from k over the inner counter J from k + 1 by 1 of nn steps, whose final value j is at least n (the exit)
// while its values stay below n (the constraint, bound twice, since a closed side condition is decided, not matched)
lemma {:rw} current_selection_swaps(a: array<int, int>, n: int, n2: int, ks: List<int>, is: List<int>, ms: List<int>,
                                    Ms: List<Trace<int>>, Js: List<Trace<int>>, Js2: List<Trace<int>>,
                                    Ns: List<Nat>, js: List<int>)
  requires invs(for ks, ms, Ms check k, m, M :: m == current(M))
  requires invs(for ks, ⌊trace(a, for ks, is, ms do b, k, i, m :: b[k := b[m]][m := b[k]])⌋, Ms, Js check k, b, M, J ::
    M == trace(k, for ⌊J⌋ do m, j :: case b[j] < b[m] => j case b[m] <= b[j] => m))
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(k + 1, 1, nn))
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn) + k + 1)
  requires invs(for ks, js check k, j :: n <= j)
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j < n2))
  requires Js2 == Js && n2 == n
  ensures current(trace(a, for ks, is, ms do b, k, i, m :: b[k := b[m]][m := b[k]]))
    == current(trace(a, for ks do b, k :: b[k := b[argmin(b, k, n)]][argmin(b, k, n) := b[k]]))

// all of b[lo..mid) are at most all of b[mid..hi)
function partitioned(b: array<int, int>, lo: int, mid: int, hi: int): bool

// the empty prefix is sorted and partitioned from the rest
lemma {:rw} sorted_empty(b: array<int, int>, lo: int)
  ensures sorted(b, lo, lo) <==> true

lemma {:rw} partitioned_empty(b: array<int, int>, lo: int, hi: int)
  ensures partitioned(b, lo, lo, hi) <==> true

// one step of selection sort: the swap of k with the position of the minimum of b[k..n) extends a sorted prefix
// b[0..k) that is partitioned from b[k..n) by one position, and keeps it partitioned
lemma {:rw} sorted_swap_argmin(b: array<int, int>, k: int, n: int)
  requires k < n && sorted(b, 0, k) && partitioned(b, 0, k, n)
  ensures sorted(b[k := b[argmin(b, k, n)]][argmin(b, k, n) := b[k]], 0, k + 1) <==> true

lemma {:rw} partitioned_swap_argmin(b: array<int, int>, k: int, n: int)
  requires k < n && sorted(b, 0, k) && partitioned(b, 0, k, n)
  ensures partitioned(b[k := b[argmin(b, k, n)]][argmin(b, k, n) := b[k]], 0, k + 1, n) <==> true

// the induction for sorting by a growing sorted prefix: the steps F keep the prefix b[0..k) sorted and
// partitioned from b[k..n) while extending it, hence exactly n steps sort b[0..n) (the number of steps is the
// length, as the goal states it, since further steps would be unconstrained)
lemma {:rw} sorted_prefix_steps(a: array<int, int>, n: int, m: Nat, F: (array<int, int>, int) -> array<int, int>)
  requires n == integer(m)
  requires forall b: array<int, int>, k: int :: 0 <= k < n && sorted(b, 0, k) && partitioned(b, 0, k, n)
    ==> sorted(F(b, k), 0, k + 1) && partitioned(F(b, k), 0, k + 1, n)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋ do b, k :: F(b, k))), 0, n) <==> true

// a trace of swaps over one dependency preserves the permutation (perm_swaps of perm.dfy for one dependency)
lemma {:rw} perm_swaps_one(a: array<int, int>, b: array<int, int>, ks: List<int>,
                           P: (array<int, int>, int) -> int, Q: (array<int, int>, int) -> int)
  ensures perm(current(trace(a, for ks do x, k :: x[P(x, k) := x[Q(x, k)]][Q(x, k) := x[P(x, k)]])), b)
    <==> perm(a, b)

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var j: int;
  var m: int;
  var t: int;
  b := a;
  i := 0;
  while i < n
  {
    m := i;
    j := i + 1;
    while j < n
    {
      if b[j] < b[m] {
        m := j;
      }
      j := j + 1;
    }
    t := b[i];
    b[i] := b[m];
    b[m] := t;
    i := i + 1;
  }
}
