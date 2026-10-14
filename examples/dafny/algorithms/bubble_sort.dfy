// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/bubble_sort.dfy
// bubble sort with nested loops: the outer loop moves the bound i down, the inner loop swaps adjacent elements
// out of order below it
//
// status (Oct 14, 2026): -teq -prove leaves one goal, the postcondition sorted(b, 0, n) && perm(b, a); the inner
// loop is a value of the outer update since -teq closes nested loops, so the lemmas below, written for -simplify on
// the per-variable form, where the inner loop was fragments of the outer iteration constraint (verified that way on
// Oct 11, 2026, NOTES.md, doc/array-algorithms), no longer match; the module teq:nested of those fragments is retired
// to resources/cuvee/legacy (the goal is the same with and without it)

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// one pass of bubble sort over the positions js: adjacent elements out of order are swapped
function {:fold} bubble_pass(b: array<int, int>, js: List<int>): Trace<array<int, int>>
{
  trace(b, for js do x, j :: case x[j + 1] < x[j] => x[j := x[j + 1]][j + 1 := x[j]] case x[j] <= x[j + 1] => x)
}

lemma {:rw} perm_bubble_pass(b: array<int, int>, c: array<int, int>, js: List<int>)
  ensures perm(current(bubble_pass(b, js)), c) <==> perm(b, c)

// the values of a variable at the head of an outer loop whose body only runs an inner loop on it:
// the initial value followed by the results bs of the inner loop
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// the summary of the inner loop: in iteration k of the outer loop, the inner loop is a bubble pass over the
// positions 0, ..., len - k - 2 (len - k - 1 positions, arithmetic on the bound variable k, which the right-hand side
// may contain), given its trace equations and iteration constraints as side conditions:
// the exit len <= j + k + 1 of the inner loop binds len, its test j + k + 1 < len holds for the positions visited,
// J is the inner counter from 0 by 1 of nn steps and j == integer(nn) its final value (the forms that the module
// nested of the lemma database gives the fragments), and each result b is the current value of a pass B that
// starts from the previous result x
lemma {:rw} current_results_bubble(a: array<int, int>, len: int, ks: List<int>, js: List<int>, Js: List<Trace<int>>,
                                   Js2: List<Trace<int>>, js3: List<int>, Ns: List<Nat>, Ns2: List<Nat>,
                                   bs: List<array<int, int>>, Bs: List<Trace<array<int, int>>>)
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Bs, Js check k, x, B, J :: B == bubble_pass(x, ⌊J⌋))
  requires invs(for ks, js check k, j :: len <= j + k + 1)
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j + k + 1 < len))
  requires Js2 == Js
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(0, 1, nn))
  requires invs(for ks, Ns2, js3 check k, nn, j :: j == integer(nn))
  requires Ns2 == Ns && js3 == js
  ensures current(results(a, ks, bs))
    == current(trace(a, for ks do b, k :: current(bubble_pass(b, ⌊counter(0, 1, natural(len - k - 1))⌋))))

// a trace of steps that preserve the permutation
lemma {:rw} perm_steps(a: array<int, int>, c: array<int, int>, ks: List<int>, F: (array<int, int>, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int :: perm(F(b, k), b)
  ensures perm(current(trace(a, for ks do b, k :: F(b, k))), c) <==> perm(a, c)

// the invariant of the outer loop after k passes: the suffix b[len - k..len) is sorted and all of b[0..len - k) are
// at most all of it, where the suffix is all of b[0..len) once k reaches len; a predicate indexed by the iteration,
// such that the induction below ranges over all iterations without a case distinction on k
function bubbled(b: array<int, int>, k: int, len: int): bool

// one pass over the positions 0, ..., p - 1 for p == len - k - 1 moves the maximum of b[0..p] to p, which extends
// the sorted suffix by p (for p <= 0 the pass is empty, and the suffix is the whole range already); p is a variable
// with the equation as a side condition, since a pattern len - k - 1 with two variables is not matched
lemma {:rw} bubbled_pass(b: array<int, int>, p: int, k: int, len: int)
  requires p == len - k - 1 && bubbled(b, k, len)
  ensures bubbled(current(bubble_pass(b, ⌊counter(0, 1, natural(p))⌋)), k + 1, len) <==> true

// the induction for bubble sort: the steps F keep the invariant from one iteration to the next, hence m steps sort
// b[0..len) if len <= m + 1 (the invariant holds initially by its definition)
lemma {:rw} sorted_bubbled_steps(a: array<int, int>, len: int, m: Nat, F: (array<int, int>, int) -> array<int, int>)
  requires len <= integer(m) + 1
  requires forall b: array<int, int>, k: int :: 0 <= k < integer(m) && bubbled(b, k, len) ==> bubbled(F(b, k), k + 1, len)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋ do b, k :: F(b, k))), 0, len) <==> true

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var j: int;
  var t: int;
  b := a;
  i := n;
  while 1 < i
  {
    j := 0;
    while j + 1 < i
    {
      if b[j + 1] < b[j] {
        t := b[j];
        b[j] := b[j + 1];
        b[j + 1] := t;
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
