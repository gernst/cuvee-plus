// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/nested_sum.dfy
// the result of the inner loop is used once per outer iteration: c is the sum of m times n
//
// status: verified with -teq -simplify by the generic fragment lemmas of fragments.dfy, which rewrite the fragments
// of the iteration constraint of the outer loop that describe the inner loop (see invs_counter_equation.dfy and
// invs_fragments.dfy for the two problems of nested loops, which they work around): J == sums(0, maps(for ⌊K⌋ yield 1))
// becomes J == counter(0, 1, nn) through the fragment K == counter(0, 1, nn), j == current(J) becomes
// j == integer(nn), the inner iteration constraint invs(for ⌊J⌋ check j :: j < n) becomes integer(nn) <= n, and the
// exit n <= j together with it j == n in each iteration; then consts_prefix_def and sum_consts_prefix of teq.dfy give sum(J?) == n * m;
// the remaining integer(n') * n == m * n with integer(n') == m needs mul_eq_cancel, since the simplifier does not
// substitute the solution of the equation into the product (the other instance of this problem: is_sorted.dfy)

// the inner counter: a variable increased by c over the inner counter K, which is counter(0, 1, nn) in the same
// iteration, is a counter from its initial value X(k) (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the final value of an inner counter (fragments.dfy)
lemma {:rw} invs_current_counter(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: int -> int, c: int)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, Ns, js check k, nn, j :: j == X(k) + integer(nn) * c)

// the iteration constraint of an inner counter from 0 by 1 below a nonnegative bound (fragments.dfy)
lemma {:rw} invs_invs_counter_upper_zero(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, n: int)
  requires 0 <= n
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(0, 1, nn))
  ensures invs(for ks, Js check k, J :: invs(for ⌊J⌋ check x :: x < n))
    <==> invs(for ks, Ns check k, nn :: integer(nn) <= n)

// the exit of an inner counter from 0 by 1 at or above its bound: the inner loop stops at the bound (fragments.dfy)
lemma {:rw} invs_exit_counter_zero(ks: List<int>, Ns: List<Nat>, js: List<int>, n: int)
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn))
  requires invs(for ks, Ns check k, nn :: integer(nn) <= n)
  ensures invs(for ks, js check k, j :: n <= j)
    <==> invs(for ks, js check k, j :: j == n)

// a common factor cancels in an equation
lemma {:rw} mul_eq_cancel(a: int, b: int, n: int)
  ensures (a * n == b * n) <==> (n == 0 || a == b)

method main(m: int, n: int) returns (c: int)
  requires 0 <= m && 0 <= n
  ensures c == m * n
{
  var i: int;
  var j: int;
  c := 0;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      j := j + 1;
    }
    c := c + j;
    i := i + 1;
  }
}
