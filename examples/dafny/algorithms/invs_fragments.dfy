// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/invs_fragments.dfy
// the facts of invs_counter_equation.dfy with the inner counter inlined into the trace of J, which is then recognized
// as counter(0, 1, nn), and the inner iteration constraint is resolved to integer(nn) == 0 || 0 < n && integer(nn) <= n
//
// status: open; the goal that remains shows the second problem of nested loops: the invs is distributed over its
// conjuncts, each with the dependencies it uses (J == counter(0, 1, nn) over Ns, Js; j == current(J) over Js, js;
// the bound on nn over Ns; n <= j over js), and the fragments do not share their facts, since the body of an invs
// assumes only the invariants whose dependencies are among its own (Simplify.invariants); hence j == current(J) is
// not rewritten to j == integer(nn), and the conclusion j == n, which needs all four fragments at the same position k,
// is not derived; all fragments range over the same counter ⌊counter(0, 1, m)⌋, so the facts of a fragment hold at
// position k of the others with its other dependencies instantiated by earlier(natural(k), Z), cf. the fallback
// of the paper, invs(for Z check z :: φ) <==> forall j < steps :: φ[earlier(j, Z)]

method test(n: int, m: Nat, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>)
  requires 0 <= n
{
  assume invs(for ⌊counter(0, 1, m)⌋, Ns, Js, js check k, nn, J, j ::
    J == trace(0, for ⌊counter(0, 1, nn)⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊counter(0, 1, nn)⌋, ⌊J⌋ check i, x :: x < n) && !(j < n));
  assert invs(for ⌊counter(0, 1, m)⌋, js check k, j :: j == n);
}
