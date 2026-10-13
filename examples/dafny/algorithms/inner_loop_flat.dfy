// ./Cuvee.sh -teq -entry test -prove examples/dafny/algorithms/inner_loop_flat.dfy
// the facts of one inner loop at the top level, without sequences: the counter K, the trace of j over it, its
// current value, the iteration constraint, and the exit; closed by the lemmas of teq.dfy, j == n follows
//
// status: verified with -teq -simplify (compare invs_counter_equation.dfy, the same facts inside an invs)

method test(n: int, nn: Nat, K: Trace<int>, J: Trace<int>, j: int)
  requires 0 <= n
{
  assume K == counter(0, 1, nn) && J == trace(0, for ⌊K⌋ do x, i :: x + 1) && j == current(J)
    && invs(for ⌊K⌋, ⌊J⌋ check i, x :: x < n) && !(j < n);
  assert j == n;
}
