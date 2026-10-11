// ./Cuvee.sh -teq -include teq:nested -simplify examples/dafny/algorithms/invs_counter_equation.dfy
// the facts of inner_loop_flat.dfy inside an iteration constraint of an outer loop, as -teq produces them for nested
// loops: the inner loop's variables K, nn, J, j are bound variables of the invs over fresh sequences Ks, Ns, Js, js
//
// status: verified since the module nested of the lemma database (Oct 11, 2026) resolves the fragments by generic
// lemmas (invs_sums_counter, invs_current_counter, invs_invs_counter_upper_zero, invs_exit_counter_zero), the
// method's sequences named apart from the variables of those lemmas (NOTES.md, finding 9); the problem of the
// simplifier remains: the equation K == counter(0, 1, nn) of the bound variable K is not followed when the sibling
// conjunct J == trace(0, for ⌊K⌋ do x, i :: x + 1) is simplified, which becomes sums(0, maps(for ⌊K⌋ yield i :: 1))
// by the generic fold of sums instead of counter(0, 1, nn) by counter_def (at the top level, in inner_loop_flat.dfy,
// the equation is followed); the invs is then distributed over its conjuncts, each with the dependencies it uses,
// see invs_fragments.dfy

method test(n: int, m: Nat, KK: List<Trace<int>>, NN: List<Nat>, JJ: List<Trace<int>>, jj: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, KK, NN, JJ, jj check k, K, nn, J, j ::
    K == counter(0, 1, nn) && J == trace(0, for ⌊K⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊K⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, jj check k, j :: j == n);
}
