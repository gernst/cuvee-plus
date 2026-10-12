// ./Cuvee.sh -teq -entry main -include teq:nested -simplify examples/dafny/algorithms/insertion_sort.dfy
// insertion sort with nested loops: the inner loop moves b[i] down by adjacent swaps while it is smaller than its
// predecessor
//
// status: verified with -teq -simplify, both sorted(b, 0, n) and perm(b, a);
// the inner loop swaps b[j] and b[j - 1], arithmetic on a bound variable of the trace, which no pattern matches
// (TODO.md), hence the summary lemma current_results_insert takes the positions of the swaps as higher-order P(y, j)
// and Q(y, j), like perm_results_swaps before it, and pins them to j and j - 1 by quantified side conditions, which
// the simplifier decides by beta reduction (the workaround for every literal pattern that is not matched, also the
// disjunctive guard of merge.dfy); likewise the test y[j] < y[j - 1] of the inner loop is a higher-order D(y, j),
// pinned, and stated apart from 0 < j, since the simplifier splits the constraint into two fragments; otherwise as
// insertion_sort2.dfy (two pointers), whose summary has the positions as counters: the inner counter J from i down by
// 1 by invs_sums_counter of fragments.dfy, the exit on the final values, the duplicate-variable trick for closed
// side conditions, the induction sorted_prefix_steps_two with sorted_insert, and perm_steps_two with perm_insert

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the inner counter (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// the insertion of b[i] into b[0..i)
function insert(b: array<int, int>, i: int): array<int, int>

// the summary of the inner loop with one pointer: the swaps are at the positions P(y, j) and Q(y, j), higher-order,
// pinned to j and j - 1 by quantified side conditions, since a pattern y[j := y[j - 1]] with arithmetic on the bound
// variable j is not matched (TODO.md); likewise the test D(b, j) of the loop
lemma {:rw} current_results_insert(a: array<int, int>, d: int, ks: List<int>, is: List<int>, bs: List<array<int, int>>,
                                   Bs: List<Trace<array<int, int>>>, Js: List<Trace<int>>, Ns: List<Nat>, Ns2: List<Nat>, js: List<int>,
                                   Js3: List<Trace<int>>, Bs5: List<Trace<array<int, int>>>, Js5: List<Trace<int>>,
                                   bs6: List<array<int, int>>, js6: List<int>, Js7: List<Trace<int>>,
                                   P: (array<int, int>, int) -> int, Q: (array<int, int>, int) -> int, D: (array<int, int>, int) -> bool)
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Bs, Js check k, x, B, J ::
    B == trace(x, for ⌊J⌋ do y, j :: y[P(y, j) := y[Q(y, j)]][Q(y, j) := y[P(y, j)]]))
  requires forall y: array<int, int>, j: int :: P(y, j) == j
  requires forall y: array<int, int>, j: int :: Q(y, j) == j - 1
  requires invs(for is, Ns, Js3 check i, nn, J :: J == counter(i, d, nn))
  requires Js3 == Js && d == -1
  requires invs(for ks, is check k, i :: i == k + 1)
  // the final values of the counter in the form that the module nested gives them, j == i - nn (without the module the
  // fragment is j == current(J), and the summary was stated with it)
  requires invs(for ks, Ns2, js check k, nn, j :: integer(nn) + j == k + 1)
  requires Ns2 == Ns
  requires invs(for ks, Js7 check k, J :: invs(for ⌊J⌋ check j :: 0 < j))
  requires Js7 == Js
  requires invs(for ks, Bs5, Js5 check k, B, J :: invs(for ⌊B⌋, ⌊J⌋ check y, j :: D(y, j)))
  requires Bs5 == Bs && Js5 == Js
  requires forall y: array<int, int>, j: int :: D(y, j) <==> y[j] < y[j - 1]
  requires invs(for ks, bs6, js6 check k, b, j :: !(0 < j && D(b, j)))
  requires bs6 == bs && js6 == js
  ensures current(results(a, ks, bs)) == current(trace(a, for ks, is do b, k, i :: insert(b, i)))

lemma {:rw} perm_insert(b: array<int, int>, c: array<int, int>, i: int)
  ensures perm(insert(b, i), c) <==> perm(b, c)

lemma {:rw} perm_steps_two(a: array<int, int>, c: array<int, int>, ks: List<int>, is: List<int>,
                           F: (array<int, int>, int, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int, i: int :: perm(F(b, k, i), b)
  ensures perm(current(trace(a, for ks, is do b, k, i :: F(b, k, i))), c) <==> perm(a, c)

lemma {:rw} sorted_insert(b: array<int, int>, i: int)
  requires sorted(b, 0, i)
  ensures sorted(insert(b, i), 0, i + 1) <==> true

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
  var t: int;
  b := a;
  i := 1;
  while i < n
  {
    j := i;
    while 0 < j && b[j] < b[j - 1]
    {
      t := b[j];
      b[j] := b[j - 1];
      b[j - 1] := t;
      j := j - 1;
    }
    i := i + 1;
  }
}
