// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/row_sums.dfy
// the sums of the rows of an m x n matrix: nested loops, the inner loop sums one row, the outer loop stores the sum
//
// status: verified with -teq -simplify; the inner loop becomes fragments of the iteration constraint of the outer
// loop (NOTES.md), which the generic fragment lemmas of fragments.dfy resolve: the inner counter J, its final value
// j == n, hence the numbers of inner iterations N? == ⌊consts(m, natural(n))⌋; the two new lemmas substitute the
// definition of a sequence into another fragment about it (invs_subst_counter: the trace T == sums(0, selects(A[k], ⌊J⌋))
// of the sum becomes one over the counter, invs_subst_sums: the result t == current(T) becomes the sum), such that
// the final values are t == sum(selects(A[k], ⌊counter(0, 1, natural(n))⌋)) in each iteration; the postcondition
// reads the stored result at position i, earlier(natural(i), T?), which earlier_invs_def instantiates (the paper's
// instantiation of an invariant at a witness)

// the inner counter (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// a fragment about the inner counter J, which is counter(X(k), c, nn) in the same iteration, is stated about the
// counter: the final value j == current(J), or a trace of the inner loop over ⌊J⌋
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

// a fragment about the inner results T, which are sums in the same iteration, is stated about the sums
lemma {:rw} invs_subst_sums<a>(ks: List<int>, hs: List<int>, Ts: List<Trace<int>>, ts: List<a>, x: int, V: (int, int) -> List<int>, F: (int, Trace<int>) -> a)
  requires invs(for ks, hs, Ts check k, h, T :: T == sums(x, V(k, h)))
  ensures invs(for ks, Ts, ts check k, T, t :: t == F(k, T))
    <==> invs(for ks, hs, ts check k, h, t :: t == F(k, sums(x, V(k, h))))

// the element at a position of a sequence whose elements are given by the iterations
lemma {:rw} earlier_invs_def<a>(m: Nat, ts: List<a>, i: int, F: int -> a)
  requires invs(for ⌊counter(0, 1, m)⌋, ts check k, t :: t == F(k))
  requires 0 <= i < integer(m)
  ensures earlier(natural(i), ts) == F(i)

method main(A: array<int, array<int, int>>, m: int, n: int) returns (s: array<int, int>)
  requires 0 <= m && 0 <= n
  ensures forall i: int :: 0 <= i < m ==> s[i] == sum(selects(A[i], ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  var t: int;
  i := 0;
  while i < m
  {
    t := 0;
    j := 0;
    while j < n
    {
      t := t + A[i][j];
      j := j + 1;
    }
    s := s[i := t];
    i := i + 1;
  }
}
