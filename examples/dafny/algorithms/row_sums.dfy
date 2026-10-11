// ./Cuvee.sh -teq -include teq:nested -simplify examples/dafny/algorithms/row_sums.dfy
// the sums of the rows of an m x n matrix: nested loops, the inner loop sums one row, the outer loop stores the sum
//
// status: verified with -teq -include teq:nested -simplify (Oct 11, 2026, evening); the module nested resolves the
// inner counter J == counter(0, 1, nn), the exit (abstracted to consts_prefix(m, n, J?)) and the numbers of inner
// iterations N? == ⌊consts(m, natural(n))⌋; the lemmas below are the chain from there to the postcondition, one
// specific lemma per step and no general left-hand side: the counters over the constant numbers of iterations, the
// inner sums over the inner counter, the final values of the inner traces (t == current(T) with T given per
// iteration), the sums given per iteration as a maps, and the element of a maps over the counter at the position i
// of the postcondition; each takes the fragment it depends on as a side condition over a fresh list variable,
// identified with the list of the left-hand side by an equation (a closed invs condition is decided, not matched);
// the earlier substitution lemmas invs_subst_counter, invs_subst_sums, and earlier_invs_def had general left-hand
// sides (a higher-order body, a read earlier(natural(i), ts)) with an invs side condition over the lists of the
// left-hand side, which is matched in the context of the fact's combinator, whose reads the same rules match again:
// the run did not terminate (NOTES.md, finding 19)
// the inner counters over the constant numbers of iterations, the dependency as a pattern matched through the context
// (N? == ⌊consts(m, natural(n))⌋ is a hypothesis, from invs_natural_consts of the module nested)
lemma {:rw} invs_counter_consts(ks: List<int>, Js: List<Trace<int>>, m: Nat, n: int)
  requires 0 <= n
  ensures invs(for ks, ⌊consts(m, natural(n))⌋, Js check k, nn, J :: J == counter(0, 1, nn))
    <==> invs(for ks, Js check k, J :: J == counter(0, 1, natural(n)))

// the same with the sequence as a variable and its definition as a side condition
lemma {:rw} invs_counter_consts_var(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, m: Nat, n: int)
  requires Ns == ⌊consts(m, natural(n))⌋
  requires 0 <= n
  ensures invs(for ks, Ns, Js check k, nn, J :: J == counter(0, 1, nn))
    <==> invs(for ks, Js check k, J :: J == counter(0, 1, natural(n)))

// the inner sums over the inner counter, whose fragment is a side condition over a fresh variable
lemma {:rw} invs_sums_selects_counter(ks: List<int>, Ts: List<Trace<int>>, Js: List<Trace<int>>, Js2: List<Trace<int>>, n: int,
                                      F: int -> array<int, int>)
  requires invs(for ks, Js2 check k, J :: J == counter(0, 1, natural(n)))
  requires Js2 == Js
  ensures invs(for ks, Ts, Js check k, T, J :: T == sums(0, selects(F(k), ⌊J⌋)))
    <==> invs(for ks, Ts check k, T :: T == sums(0, selects(F(k), ⌊counter(0, 1, natural(n))⌋)))

// the final values of inner traces given per iteration (invs_current_counter of the nested module for any trace)
lemma {:rw} invs_current_def(ks: List<int>, ts: List<int>, Ts: List<Trace<int>>, Ts2: List<Trace<int>>, G: int -> Trace<int>)
  requires invs(for ks, Ts2 check k, T :: T == G(k))
  requires Ts2 == Ts
  ensures invs(for ks, ts, Ts check k, t, T :: t == current(T))
    <==> invs(for ks, ts check k, t :: t == current(G(k)))

// a sequence of sums given per iteration is the map of them (specific to sums, so that the fragments of the
// final values of counters, j == current(J), are left to the lemmas above)
lemma {:rw} invs_maps_sum(ks: List<int>, ts: List<int>, F: int -> List<int>)
  ensures invs(for ks, ts check k, t :: t == sum(F(k))) <==> ts == maps(for ks yield k :: sum(F(k)))

// the element of a map over the counter at a position of the counter
lemma {:rw} earlier_maps_counter(i: int, m: Nat, F: int -> int)
  requires 0 <= i < integer(m)
  ensures earlier(natural(i), maps(for ⌊counter(0, 1, m)⌋ yield k :: F(k))) == F(i)

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
