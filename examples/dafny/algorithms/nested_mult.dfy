// ./Cuvee.sh -teq -entry main -include teq:nested -simplify examples/dafny/algorithms/nested_mult.dfy
// multiplication by repeated addition: the inner loop increments the outer variable n times
//
// status: verified with -teq -simplify; the inner loop modifies the outer variable r, whose outer trace is the
// chain of the inner results, R == results(0, ⌊K⌋, R?), with r' == current(R') and
// R' == sums(r, maps(for ⌊K'⌋ yield 1)) in the fragments, where the initial value r is bound to the outer trace ⌊R⌋;
// the generic fragment lemmas of fragments.dfy give R' == counter(r, 1, nn) over ⌊R⌋ (the matcher selects ⌊R⌋ as the
// first dependency, since the initial value is its bound variable), hence invs_current_counter_other for
// r' == r + integer(nn), the fragments of the inner counter j give j == n, hence n == integer(nn) in each iteration,
// which invs_integer_consts turns into N? == ⌊consts(m, natural(n))⌋, substituted into r' == r + integer(nn), so that
// r' == r + n; then current_results_steps makes the outer trace the trace of the steps r + n, a counter by n, whose
// current value is n * m; the lemma is monomorphic, since a polymorphic lemma with a higher-order variable in its
// side condition is not matched (also not F(x) alone); mul_eq_cancel as in nested_sum.dfy

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

// the same for a counter whose fragment ranges over another first dependency hs than the counter ks of the outer
// loop, here the outer trace of r, whose value is the initial value of the inner counter (fragments.dfy)
lemma {:rw} invs_current_counter_other<a>(ks: List<int>, hs: List<a>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: a -> int, c: int)
  requires invs(for hs, Ns, Js check h, nn, J :: J == counter(X(h), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, hs, Ns, js check k, h, nn, j :: j == X(h) + integer(nn) * c)

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

// the numbers of iterations of the inner loops are all n: the sequence is constant (fragments.dfy)
lemma {:rw} invs_integer_consts(m: Nat, Ns: List<Nat>, n: int)
  requires 0 <= n
  ensures invs(for ⌊counter(0, 1, m)⌋, Ns check k, nn :: n == integer(nn))
    <==> Ns == ⌊consts(m, natural(n))⌋

// the values of a variable at the head of an outer loop whose body only runs an inner loop on it:
// the initial value followed by the results bs of the inner loop (bubble_sort.dfy)
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// the results of the inner loop are a function F of the previous value and the iteration: the outer trace is the
// trace of F; monomorphic, since a polymorphic lemma with a higher-order variable in its side condition is not matched
lemma {:rw} current_results_steps(x0: int, ks: List<int>, bs: List<int>, F: (int, int) -> int)
  requires invs(for ks, ⌊results(x0, ks, bs)⌋, bs check k, x, b :: b == F(x, k))
  ensures current(results(x0, ks, bs)) == current(trace(x0, for ks do x, k :: F(x, k)))

// a common factor cancels in an equation
lemma {:rw} mul_eq_cancel(a: int, b: int, n: int)
  ensures (a * n == b * n) <==> (n == 0 || a == b)

method main(m: int, n: int) returns (r: int)
  requires 0 <= m && 0 <= n
  ensures r == m * n
{
  var i: int;
  var j: int;
  r := 0;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      r := r + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
