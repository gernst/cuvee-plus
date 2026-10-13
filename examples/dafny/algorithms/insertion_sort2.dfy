// ./Cuvee.sh -teq -entry main -include teq:nested -prove examples/dafny/algorithms/insertion_sort2.dfy
// insertion sort with nested loops, with two pointers j and p == j - 1 in the inner loop, such that the positions
// of the swaps are counters: insertion_sort.dfy swaps b[j] and b[j - 1], arithmetic on a bound variable of the
// trace, which patterns do not match (TODO.md), hence its inner loop cannot be summarized (the principle of
// reverse.dfy: two pointers instead of index arithmetic)
//
// status: verified with -teq -simplify, both sorted(b, 0, n) and perm(b, a);
// the outer array trace is the chain of the results of the inner loop, B == results(a, ⌊K⌋, B?), and the inner loop
// is a trace of swaps B' == trace(b, for ⌊J⌋, ⌊P⌋ do y, j, p :: y[j := y[p]][p := y[j]]) over the counters J from i
// and P from k == i - 1 down by 1, which invs_sums_counter of fragments.dfy recognizes, with the iteration
// constraints 0 < j and y[j] < y[p], and the exit !(0 < j && b'[j] < b'[p]) on the final values; the summary lemma
// current_results_insert takes all of them as side conditions, matched against the facts (as current_results_bubble
// in bubble_sort.dfy, with duplicates identified by equations, since a closed side condition is decided, not
// matched; the relation i == k + 1 of the two counters is a closed side condition that the simplifier decides), and
// rewrites the outer trace into the trace of insert(b, i), the insertion of b[i] into b[0..i), an abstract function;
// sorted(b, 0, n) then follows from sorted_prefix_steps_two, a generic induction over a trace of steps at the
// positions i of a second counter that extend a sorted prefix, whose quantified side condition the simplifier
// decides by sorted_insert (the side condition must not state i == k + 1: the simplifier substitutes it, and the
// pattern sorted(insert(b, i), 0, i + 1) does not match sorted(insert(b, k + 1), 0, k + 2)); perm(b, a) from
// perm_steps_two and perm_insert

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the inner counters: a variable increased by c over the inner counter K, which is counter(0, 1, nn) in the same
// iteration, is a counter from its initial value X(k) (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the outer trace: the initial value followed by the results of the inner loop (bubble_sort.dfy)
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// the insertion of b[i] into b[0..i): b[i] moves down by adjacent swaps while it is smaller than its predecessor
function insert(b: array<int, int>, i: int): array<int, int>

// the summary of the inner loop: in iteration k, the inner loop inserts b[i] for i == k + 1, given its trace
// equations and iteration constraints as side conditions: the result b is the current value of a trace B of swaps
// of the positions j and p from x, which are counters down by 1 from i and from k, i.e. p == j - 1, the final
// values j and p of which fail the test, which holds for the positions visited; the step d of the counters is a
// variable with d == -1 as a side condition, since the literal -1 in a pattern is not matched (reverse.dfy)
lemma {:rw} current_results_insert(a: array<int, int>, d: int, ks: List<int>, is: List<int>, bs: List<array<int, int>>,
                                   Bs: List<Trace<array<int, int>>>, Js: List<Trace<int>>, Ps: List<Trace<int>>,
                                   Ns: List<Nat>, Ns2: List<Nat>, Js2: List<Trace<int>>, js: List<int>, Ns3: List<Nat>,
                                   ps: List<int>, Ns4: List<Nat>, Js4: List<Trace<int>>,
                                   Bs5: List<Trace<array<int, int>>>, Js5: List<Trace<int>>, Ps5: List<Trace<int>>,
                                   bs6: List<array<int, int>>, js6: List<int>, ps6: List<int>)
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Bs, Js, Ps check k, x, B, J, P ::
    B == trace(x, for ⌊J⌋, ⌊P⌋ do y, j, p :: y[j := y[p]][p := y[j]]))
  requires invs(for ks, Ns, Ps check k, nn, P :: P == counter(k, d, nn))
  requires d == -1
  requires invs(for is, Ns2, Js2 check i, nn, J :: J == counter(i, d, nn))
  requires Ns2 == Ns && Js2 == Js
  requires invs(for ks, is check k, i :: i == k + 1)
  // the final values of the counters in the forms that the module nested gives them, j == i - nn and p == k - nn, with
  // the numbers of iterations over a fresh variable identified with Ns (without the module the fragments are
  // j == current(J) and p == current(P), and the summary was stated with them)
  requires invs(for ks, Ns3, js check k, nn, j :: integer(nn) + j == k + 1)
  requires Ns3 == Ns
  requires invs(for ks, Ns4, ps check k, nn, p :: integer(nn) + p == k)
  requires Ns4 == Ns
  requires invs(for ks, Js4 check k, J :: invs(for ⌊J⌋ check j :: 0 < j))
  requires Js4 == Js
  requires invs(for ks, Bs5, Js5, Ps5 check k, B, J, P :: invs(for ⌊B⌋, ⌊J⌋, ⌊P⌋ check y, j, p :: y[j] < y[p]))
  requires Bs5 == Bs && Js5 == Js && Ps5 == Ps
  requires invs(for ks, bs6, js6, ps6 check k, b, j, p :: !(0 < j && b[j] < b[p]))
  requires bs6 == bs && js6 == js && ps6 == ps
  ensures current(results(a, ks, bs)) == current(trace(a, for ks, is do b, k, i :: insert(b, i)))

// an insertion is a permutation
lemma {:rw} perm_insert(b: array<int, int>, c: array<int, int>, i: int)
  ensures perm(insert(b, i), c) <==> perm(b, c)

// a trace of steps that preserve the permutation, over two dependencies (perm_steps of bubble_sort.dfy)
lemma {:rw} perm_steps_two(a: array<int, int>, c: array<int, int>, ks: List<int>, is: List<int>,
                           F: (array<int, int>, int, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int, i: int :: perm(F(b, k, i), b)
  ensures perm(current(trace(a, for ks, is do b, k, i :: F(b, k, i))), c) <==> perm(a, c)

// an insertion into a sorted prefix extends it
lemma {:rw} sorted_insert(b: array<int, int>, i: int)
  requires sorted(b, 0, i)
  ensures sorted(insert(b, i), 0, i + 1) <==> true

// the induction for sorting by a growing sorted prefix from one element: the steps F at the positions i of a second
// counter from 1 extend the sorted prefix b[0..i) by i, for all i, hence m steps sort b[0..m + 1) and b[0..n) if
// n <= m + 1
lemma {:rw} sorted_prefix_steps_two(a: array<int, int>, n: int, m: Nat, F: (array<int, int>, int, int) -> array<int, int>)
  requires n <= integer(m) + 1
  requires forall b: array<int, int>, k: int, i: int :: 0 <= i && sorted(b, 0, i)
    ==> sorted(F(b, k, i), 0, i + 1)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋, ⌊counter(1, 1, m)⌋ do b, k, i :: F(b, k, i))), 0, n)
    <==> true

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var j: int;
  var p: int;
  var t: int;
  b := a;
  i := 1;
  while i < n
  {
    j := i;
    p := i - 1;
    while 0 < j && b[j] < b[p]
    {
      t := b[j];
      b[j] := b[p];
      b[p] := t;
      j := j - 1;
      p := p - 1;
    }
    i := i + 1;
  }
}
