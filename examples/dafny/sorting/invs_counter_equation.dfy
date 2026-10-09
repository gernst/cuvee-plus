// ./Cuvee.sh -teq -simplify examples/dafny/sorting/invs_counter_equation.dfy
// the facts of inner_loop_flat.dfy inside an iteration constraint of an outer loop, as -teq produces them for nested
// loops: the inner loop's variables K, nn, J, j are bound variables of the invs over fresh sequences Ks, Ns, Js, js
//
// status: open; the goal that remains shows the first problem of nested loops: the equation K == counter(0, 1, nn)
// of the bound variable K is not followed when the sibling conjunct J == trace(0, for ⌊K⌋ do x, i :: x + 1) is
// simplified, which becomes sums(0, maps(for ⌊K⌋ yield i :: 1)) by the generic fold of sums instead of
// counter(0, 1, nn) by counter_def (at the top level, in inner_loop_flat.dfy, the equation is followed);
// the invs is then distributed over its conjuncts, each with the dependencies it uses, see invs_fragments.dfy

method test(n: int, m: Nat, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, Ks, Ns, Js, js check k, K, nn, J, j ::
    K == counter(0, 1, nn) && J == trace(0, for ⌊K⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊K⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, js check k, j :: j == n);
}
