// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/transpose.dfy
// the transpose of an m x n matrix: nested loops that store A[i][j] at B[j][i]
//
// status: verified with -teq -simplify; row_sums.dfy on an array-valued inner result: the fragment lemmas of
// fragments.dfy resolve the inner counter and its length n, invs_subst_counter states the inner trace over the
// counter, which folds into column(B, A, k, nn), the stores of column k; invs_subst_column substitutes it into the
// result b == current(B'), current_results_steps (nested_mult.dfy, monomorphic for arrays of arrays) makes the outer
// trace the trace of the columns, and current_transpose reads the transposed element

// the inner counter (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// a fragment about the inner counter J is stated about the counter (row_sums.dfy)
lemma {:rw} invs_subst_counter<a>(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, ts: List<a>, X: int -> int, c: int, F: (int, Trace<int>) -> a)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, ts check k, J, t :: t == F(k, J))
    <==> invs(for ks, Ns, ts check k, nn, t :: t == F(k, counter(X(k), c, nn)))

// the iteration constraint of an inner counter from 0 by 1 below a nonnegative bound (fragments.dfy)
lemma {:rw} invs_invs_counter_upper_zero(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, n: int)
  requires 0 <= n
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(0, 1, nn))
  ensures invs(for ks, Js check k, J :: invs(for ⌊J⌋ check x :: x < n))
    <==> invs(for ks, Ns check k, nn :: integer(nn) <= n)

// the exit of an inner counter from 0 by 1 at or above its bound (fragments.dfy)
lemma {:rw} invs_exit_counter_zero(ks: List<int>, Ns: List<Nat>, js: List<int>, n: int)
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn))
  requires invs(for ks, Ns check k, nn :: integer(nn) <= n)
  ensures invs(for ks, js check k, j :: n <= j)
    <==> invs(for ks, js check k, j :: j == n)

// the numbers of iterations of the inner loops are all n (fragments.dfy)
lemma {:rw} invs_integer_consts(m: Nat, Ns: List<Nat>, n: int)
  requires 0 <= n
  ensures invs(for ⌊counter(0, 1, m)⌋, Ns check k, nn :: n == integer(nn))
    <==> Ns == ⌊consts(m, natural(n))⌋

// the outer trace: the initial value followed by the results of the inner loop
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// the inner loop: column k of the transpose, the stores of A[k][j] at B[j][k] for j below nn
function {:fold} column(B0: array<int, array<int, int>>, A: array<int, array<int, int>>, k: int, nn: Nat): Trace<array<int, array<int, int>>>
{
  trace(B0, for ⌊counter(0, 1, nn)⌋ do B, j :: B[j := B[j][k := A[k][j]]])
}

// a fragment about the inner results B', which are columns in the same iteration, is stated about the columns
lemma {:rw} invs_subst_column(ks: List<int>, hs: List<array<int, array<int, int>>>, Ns: List<Nat>, Bs: List<Trace<array<int, array<int, int>>>>,
                              bs: List<array<int, array<int, int>>>, A: array<int, array<int, int>>)
  requires invs(for ks, hs, Ns, Bs check k, h, nn, B :: B == column(h, A, k, nn))
  ensures invs(for ks, Bs, bs check k, B, b :: b == current(B))
    <==> invs(for ks, hs, Ns, bs check k, h, nn, b :: b == current(column(h, A, k, nn)))

// the results of the inner loop are a function F of the previous value and the iteration (nested_mult.dfy)
lemma {:rw} current_results_steps(x0: array<int, array<int, int>>, ks: List<int>, bs: List<array<int, array<int, int>>>,
                                  F: (array<int, array<int, int>>, int) -> array<int, array<int, int>>)
  requires invs(for ks, ⌊results(x0, ks, bs)⌋, bs check k, x, b :: b == F(x, k))
  ensures current(results(x0, ks, bs)) == current(trace(x0, for ks do x, k :: F(x, k)))

// m columns transpose the m x nn matrix
lemma {:rw} current_transpose(B0: array<int, array<int, int>>, A: array<int, array<int, int>>, m: Nat, nn: Nat, i: int, j: int)
  ensures current(trace(B0, for ⌊counter(0, 1, m)⌋ do x, k :: current(column(x, A, k, nn))))[j][i]
    == if 0 <= i < integer(m) && 0 <= j < integer(nn) then A[i][j] else B0[j][i]

method main(A: array<int, array<int, int>>, m: int, n: int) returns (B: array<int, array<int, int>>)
  requires 0 <= m && 0 <= n
  ensures forall i: int, j: int :: 0 <= i < m && 0 <= j < n ==> B[j][i] == A[i][j]
{
  var i: int;
  var j: int;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      B := B[j := B[j][i := A[i][j]]];
      j := j + 1;
    }
    i := i + 1;
  }
}
