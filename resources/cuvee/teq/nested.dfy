// nested loops: the fragments of the iteration constraint of an outer loop that describe an inner loop, as -teq
// produces them, resolved by generic lemmas, and the outer trace of a variable that only the inner loop modifies from
// examples/dafny/algorithms (fragments.dfy, nested_mult.dfy, distinct.dfy), Oct 11, 2026; this file assumes the core
// declarations of teq.dfy (Nat, integer, natural, List, Trace, current, butlast, counter, earlier, consts),
// counters.dfy, and aggregation.dfy (sums); see NOTES.md there for the termination analysis of the lemmas (the side
// conditions are invs over the lists of the left-hand sides, which is safe since the left-hand sides are fragments with
// specific bodies)

// the inner counter: a variable increased by c over the inner counter K, which is counter(0, 1, nn) in the same
// iteration, is a counter from its initial value X(k), a higher-order pattern (0, k, k + 1, ...)
lemma {:rw} {:teq} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the final value of an inner counter
lemma {:rw} {:teq} invs_current_counter(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: int -> int, c: int)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, Ns, js check k, nn, j :: j == X(k) + integer(nn) * c)

// the same for a counter whose fragment ranges over another first dependency hs than the counter ks of the outer
// loop, e.g. the outer trace of the variable, since the matcher does not backtrack over the selection of the
// dependencies when a side condition fails; the positions coincide, since the dependencies have equal lengths
lemma {:rw} {:teq} invs_current_counter_other<a>(ks: List<int>, hs: List<a>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: a -> int, c: int)
  requires invs(for hs, Ns, Js check h, nn, J :: J == counter(X(h), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, hs, Ns, js check k, h, nn, j :: j == X(h) + integer(nn) * c)

// the iteration constraint of an inner counter from 0 by 1 below a nonnegative bound: the number of inner iterations
// is at most the bound; from 0 only, since the general result for X(k), if X(k) <= n then X(k) + integer(nn) <= n
// else nn == zero, is decided to k < n - integer(nn) for X(k) == k + 1, which above_iterations_def matches
lemma {:rw} {:teq} invs_invs_counter_upper_zero(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, n: int)
  requires 0 <= n
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(0, 1, nn))
  ensures invs(for ks, Js check k, J :: invs(for ⌊J⌋ check x :: x < n))
    <==> invs(for ks, Ns check k, nn :: integer(nn) <= n)

// the exit of an inner counter from 0 by 1 at or above its bound: the inner loop stops at the bound; the left-hand
// side is a bare comparison with the open bound n, which matches every comparison fragment with js synthesized as a
// map (NOTES.md, finding 15), a cost on every program, to be restated with the exit as an atom
lemma {:rw} {:teq} invs_exit_counter_zero(ks: List<int>, Ns: List<Nat>, js: List<int>, n: int)
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn))
  requires invs(for ks, Ns check k, nn :: integer(nn) <= n)
  ensures invs(for ks, js check k, j :: n <= j)
    <==> invs(for ks, js check k, j :: j == n)

// the numbers of iterations of the inner loops are all n, when the final values j == n of the inner counters are
// abstracted by consts_prefix_def of the aggregation module, which is tried first: the sequence is constant, which
// is substituted into the other fragments; the atom is the left-hand side, which binds n, and the fragment of the
// final values the side condition, which binds Ns (a variant with the body n == integer(nn) as the left-hand side
// matched any equation fragment with integer of a bound variable, and one with the atom as a side condition left n
// unbound)
lemma {:rw} {:teq} consts_prefix_integer(m: Nat, n: int, js: List<int>, Ns: List<Nat>)
  requires invs(for ⌊counter(0, 1, m)⌋, Ns, js check k, nn, j :: j == integer(nn))
  requires 0 <= n
  ensures consts_prefix(m, n, js) <==> Ns == ⌊consts(m, natural(n))⌋

// the values of a variable at the head of an outer loop whose body only runs an inner loop on it:
// the initial value followed by the results bs of the inner loop
function {:teq} {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// the results of the inner loop are a function F of the previous value and the iteration: the outer trace is the
// trace of F; monomorphic, since a polymorphic lemma with a higher-order variable in its side condition is not
// matched (TODO.md); the side condition is over the lists of the left-hand side, which cycles as soon as a lemma
// rewrites the reads earlier(natural(k), ⌊results(...)⌋) into a current (none does yet)
lemma {:rw} {:teq} current_results_steps(x0: int, ks: List<int>, bs: List<int>, F: (int, int) -> int)
  requires invs(for ks, ⌊results(x0, ks, bs)⌋, bs check k, x, b :: b == F(x, k))
  ensures current(results(x0, ks, bs)) == current(trace(x0, for ks do x, k :: F(x, k)))

// a flag that is reset whenever P fails is set at the end iff P held in all iterations (current_trace_flag for the
// conjunction of the iterations)
lemma {:rw} {:teq} current_trace_all(ks: List<int>, P: int -> bool)
  ensures current(trace(true, for ks do d, k :: if P(k) then d else false)) == invs(for ks check k :: P(k))

// the current value of a trace whose steps do not depend on the previous value is the last step
lemma {:rw} {:teq} current_trace_last(x0: bool, m: Nat, F: int -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, m)⌋ do x, k :: F(k))) == if m == zero then x0 else F(integer(m) - 1)
