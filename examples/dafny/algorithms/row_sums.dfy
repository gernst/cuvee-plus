// ./Cuvee.sh -teq -entry main -include teq:nested -simplify examples/dafny/algorithms/row_sums.dfy
// the sums of the rows of an m x n matrix: nested loops, the inner loop sums one row, the outer loop stores the sum
//
// status: verified with -teq -include teq:nested -simplify (Oct 11, 2026, evening); the module nested resolves the
// inner counter J == counter(0, 1, nn), the exit (abstracted to consts_prefix(m, n, J?)) and the numbers of inner
// iterations N? == ⌊consts(m, natural(n))⌋, and its invs_counter_consts carries the constant numbers of iterations
// into the inner counters; the two lemmas below carry the counters into the inner sums and the sums given per
// iteration into a maps, whose element at position i the lemmas on maps of a counter read; each takes the fragment it
// depends on as a side condition over a fresh list variable, identified with the list of the left-hand side by an
// equation (a closed invs condition is decided, not matched); the two lemmas were in the module nested for an
// afternoon, where they did not fire on this file although identical, while they do as lemmas of the input (NOTES.md,
// finding 34);
// the earlier substitution lemmas invs_subst_counter, invs_subst_sums, and earlier_invs_def had general left-hand
// sides (a higher-order body, a read earlier(natural(i), ts)) with an invs side condition over the lists of the
// left-hand side, which is matched in the context of the fact's combinator, whose reads the same rules match again:
// the run did not terminate (NOTES.md, finding 19)
// the inner sums over the inner counter, whose fragment is a side condition over a fresh variable
lemma {:rw} invs_sums_selects_counter(ks: List<int>, Ts: List<Trace<int>>, Js: List<Trace<int>>, Js2: List<Trace<int>>, n: int,
                                      F: int -> array<int, int>)
  requires invs(for ks, Js2 check k, J :: J == counter(0, 1, natural(n)))
  requires Js2 == Js
  ensures invs(for ks, Ts, Js check k, T, J :: T == sums(0, selects(F(k), ⌊J⌋)))
    <==> invs(for ks, Ts check k, T :: T == sums(0, selects(F(k), ⌊counter(0, 1, natural(n))⌋)))

// a sequence of sums given per iteration is the map of them, which the read earlier(natural(i), ts) of the
// postcondition then resolves by the lemmas on maps of a counter (specific to sums, so that the fragments of the final
// values of counters, j == current(J), are left to the lemmas above)
lemma {:rw} invs_maps_sum(ks: List<int>, ts: List<int>, F: int -> List<int>)
  ensures invs(for ks, ts check k, t :: t == sum(F(k))) <==> ts == maps(for ks yield k :: sum(F(k)))

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
