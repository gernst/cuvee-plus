// ./Cuvee.sh -teq -include teq:aggregation -prove examples/dafny/algorithms/fragments.dfy
// generic lemmas on the fragments of the iteration constraint of an outer loop that describe an inner loop, which
// do by rewriting what the sharing of facts between fragments (reverted in cb7aed7) did in the simplifier; the two
// methods are the facts of invs_counter_equation.dfy and invs_fragments.dfy, the minimal forms of the two problems
// of nested loops (NOTES.md), which the lemmas close; candidates for teq.dfy
//
// status: verified with -teq -simplify; the lemmas rewrite the fragments in the order in which -teq produces them:
// the trace of an inner variable over the inner counter is a counter (invs_sums_counter, from the fragment
// K == counter(0, 1, nn) as a side condition, which binds the sequence Ns of the numbers of inner iterations), the
// final value of the inner variable is its current value (invs_current_counter), the inner iteration constraint
// bounds the number of inner iterations (invs_invs_counter_upper_zero), and the exit of the inner loop together
// with that bound gives the final value (invs_exit_counter_zero); findings about the matching, see NOTES.md: the
// matcher does not backtrack over the selection of the dependencies when a side condition fails, hence the
// variant invs_current_counter_other for fragments whose first dependency is not the counter of the outer loop;
// the side conditions are stated in the normal form of the simplified facts (X(k) + integer(nn) does not match
// integer(nn), a conditional that the simplifier decides does not match its decision), hence the _zero variants;
// the result of a constraint lemma must not have the shape k < t, which above_iterations_def of teq.dfy matches with
// t synthesized as a map

// the inner counter: a variable increased by c over the inner counter K, which is counter(0, 1, nn) in the same
// iteration, is a counter from its initial value X(k)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the final value of an inner counter
lemma {:rw} invs_current_counter(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: int -> int, c: int)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, Ns, js check k, nn, j :: j == X(k) + integer(nn) * c)

// the same for a counter whose fragment ranges over another first dependency hs than the counter ks of the outer
// loop, e.g. the outer trace of the variable (nested_mult.dfy), since the matcher does not backtrack over the
// selection of the dependencies when a side condition fails; the positions coincide, since the dependencies have
// equal lengths
lemma {:rw} invs_current_counter_other<a>(ks: List<int>, hs: List<a>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: a -> int, c: int)
  requires invs(for hs, Ns, Js check h, nn, J :: J == counter(X(h), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, hs, Ns, js check k, h, nn, j :: j == X(h) + integer(nn) * c)

// the iteration constraint of an inner counter from 0 by 1 below a nonnegative bound: the number of inner iterations
// is at most the bound; from 0 only, since the general result for X(k), if X(k) <= n then X(k) + integer(nn) <= n
// else nn == zero, is decided to k < n - integer(nn) for X(k) == k + 1, which above_iterations_def of teq.dfy
// matches (selection_sort.dfy keeps the constraint as a side condition instead)
lemma {:rw} invs_invs_counter_upper_zero(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, n: int)
  requires 0 <= n
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(0, 1, nn))
  ensures invs(for ks, Js check k, J :: invs(for ⌊J⌋ check x :: x < n))
    <==> invs(for ks, Ns check k, nn :: integer(nn) <= n)

// the exit of an inner counter from 0 by 1 at or above its bound: the inner loop stops at the bound
lemma {:rw} invs_exit_counter_zero(ks: List<int>, Ns: List<Nat>, js: List<int>, n: int)
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn))
  requires invs(for ks, Ns check k, nn :: integer(nn) <= n)
  ensures invs(for ks, js check k, j :: n <= j)
    <==> invs(for ks, js check k, j :: j == n)

// the numbers of iterations of the inner loops are all n: the sequence is constant, which is substituted into the
// other fragments (nested_mult.dfy); the fact arises when j == n is assumed in the fragment j == integer(nn)
lemma {:rw} invs_integer_consts(m: Nat, Ns: List<Nat>, n: int)
  requires 0 <= n
  ensures invs(for ⌊counter(0, 1, m)⌋, Ns check k, nn :: n == integer(nn))
    <==> Ns == ⌊consts(m, natural(n))⌋

// the facts of invs_counter_equation.dfy: the inner loop's variables K, nn, J, j are bound variables of the invs
// over fresh sequences KK, NN, JJ, jj
method test_counter_equation(n: int, m: Nat, KK: List<Trace<int>>, NN: List<Nat>, JJ: List<Trace<int>>, jj: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, KK, NN, JJ, jj check k, K, nn, J, j ::
    K == counter(0, 1, nn) && J == trace(0, for ⌊K⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊K⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, jj check k, j :: j == n);
}

// the facts of invs_fragments.dfy: the inner counter inlined into the trace of J
method test_fragments(n: int, m: Nat, NN: List<Nat>, JJ: List<Trace<int>>, jj: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, NN, JJ, jj check k, nn, J, j ::
    J == trace(0, for ⌊counter(0, 1, nn)⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊counter(0, 1, nn)⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, jj check k, j :: j == n);
}
