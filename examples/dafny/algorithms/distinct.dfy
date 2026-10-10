// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/distinct.dfy
// whether the elements of a[0..n) are pairwise distinct, by a nested loop that resets a flag at a duplicate; the
// postcondition uses distincts of teq.dfy on the values at the positions of a counter
//
// status: verified with -teq -simplify; the inner loop is the flag loop of is_sorted.dfy per outer iteration, as
// fragments of the iteration constraint of the outer loop (NOTES.md), which the fragment lemmas of fragments.dfy
// rewrite (the inner counter J == counter(k + 1, 1, nn), its final value j == integer(nn) + k + 1); the summary lemma
// current_results_nodup takes the fragments as side conditions, as current_selection_swaps in selection_sort.dfy,
// and makes the outer trace the trace of the flag reset at the elements with a later duplicate, nodup(a, k, n), an
// abstract predicate; current_trace_all turns a trace of conjunctions into an iteration constraint (like
// current_trace_flag of teq.dfy), and distincts_nodup relates it to distincts of teq.dfy

// the inner counter (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the final value of an inner counter (fragments.dfy)
lemma {:rw} invs_current_counter(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: int -> int, c: int)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, Ns, js check k, nn, j :: j == X(k) + integer(nn) * c)

// the outer trace: the initial value followed by the results of the inner loop
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// whether a[k] does not occur among a[k + 1..n)
function nodup(a: array<int, int>, k: int, n: int): bool

// the summary of the inner loop: in iteration k, the flag is reset iff a[k] occurs among the later elements
lemma {:rw} current_results_nodup(a: array<int, int>, n: int, n2: int, ks: List<int>, ds: List<bool>, Ds: List<Trace<bool>>,
                                  Js: List<Trace<int>>, Js2: List<Trace<int>>, Ns: List<Nat>, js: List<int>)
  requires invs(for ks, ds, Ds check k, d, D :: d == current(D))
  requires invs(for ks, ⌊results(true, ks, ds)⌋, Ds, Js check k, x, D, J ::
    D == trace(x, for ⌊J⌋ do d, j :: case a[k] == a[j] => false case a[k] != a[j] => d))
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(k + 1, 1, nn))
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn) + k + 1)
  requires invs(for ks, js check k, j :: n <= j)
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j < n2))
  requires Js2 == Js && n2 == n
  ensures current(results(true, ks, ds)) == current(trace(true, for ks do d, k :: if nodup(a, k, n) then d else false))

// a flag that is reset whenever P fails is set at the end iff P held in all iterations
lemma {:rw} current_trace_all(ks: List<int>, P: int -> bool)
  ensures current(trace(true, for ks do d, k :: if P(k) then d else false)) == invs(for ks check k :: P(k))

// no element occurs among the later ones iff all are distinct
lemma {:rw} distincts_nodup(a: array<int, int>, m: Nat, n: int)
  requires integer(m) == n
  ensures invs(for ⌊counter(0, 1, m)⌋ check k :: nodup(a, k, n)) <==> distincts(selects(a, ⌊counter(0, 1, m)⌋))

method main(a: array<int, int>, n: int) returns (d: bool)
  requires 0 <= n
  ensures d <==> distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  d := true;
  i := 0;
  while i < n
  {
    j := i + 1;
    while j < n
    {
      if a[i] == a[j] {
        d := false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
