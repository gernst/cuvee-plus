// ./Cuvee.sh -include teq:nested -teq -simplify examples/dafny/teq/include_before_teq.dfy
// a module of the lemma database requested before -teq is injected after the modules of -teq, on which it builds,
// as with the options in the other order (algorithms/invs_counter_equation.dfy)

method test(n: int, m: Nat, KK: List<Trace<int>>, NN: List<Nat>, JJ: List<Trace<int>>, jj: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, KK, NN, JJ, jj check k, K, nn, J, j ::
    K == counter(0, 1, nn) && J == trace(0, for ⌊K⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊K⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, jj check k, j :: j == n);
}
