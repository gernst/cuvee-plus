// ./Cuvee.sh -teq -include teq:aggregation -entry test -prove examples/dafny/algorithms/invs_fragments.dfy
// the facts of invs_counter_equation.dfy with the inner counter inlined into the trace of J, which is then recognized
// as counter(0, 1, nn), and the inner iteration constraint is resolved to integer(nn) == 0 || 0 < n && integer(nn) <= n
//
// status: verified since the module nested of the lemma database (Oct 11, 2026) resolves the fragments by generic
// lemmas; the problem of the simplifier remains: the invs is distributed over its conjuncts, each with the
// dependencies it uses (J == counter(0, 1, nn) over Ns, Js; j == current(J) over Js, js; the bound on nn over Ns;
// n <= j over js), and the fragments do not share their facts, since the body of an invs assumes only the
// invariants whose dependencies are among its own (Simplify.invariants); hence j == current(J) is not rewritten to
// j == integer(nn) by the simplifier itself, and the conclusion j == n, which needs all four fragments at the same
// position k, is derived only by the lemmas; the variables of the method are named apart from the variables of the
// lemmas of the module (Ns, Js, js), whose capture made the restated exit lemma fail with "variables of a rule not
// instantiated by its match" (former NOTES.md, finding 21)

method test(n: int, m: int, NN: List<int>, JJ: List<Trace<int>>, jj: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, NN, JJ, jj check k, nn, J, j ::
    J == trace(0, for ⌊counter(0, 1, nn)⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊counter(0, 1, nn)⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, jj check k, j :: j == n);
}
