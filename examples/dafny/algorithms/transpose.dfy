// ./Cuvee.sh -teq -entry main -include teq:nested -simplify examples/dafny/algorithms/transpose.dfy
// the transpose of an m x n matrix: nested loops that store A[i][j] at B[j][i]
//
// status: verified with -teq -include teq:nested -simplify (Oct 11, 2026, evening); row_sums.dfy on an array-valued
// inner result: the module nested resolves the inner counter, the exit and the numbers of inner iterations, then
// the chain of specific lemmas: the counters over the constant numbers of iterations (invs_counter_consts of the
// module), the inner stores over the inner counter folded into column(B, A, k, natural(n)), the final values of the columns, current_results_steps
// (monomorphic for arrays of arrays) makes the outer trace the trace of the columns, and current_transpose reads the
// transposed element; the earlier substitution lemmas invs_subst_counter and invs_subst_column had general left-hand
// sides with an invs side condition over their lists and did not terminate (NOTES.md, finding 19)
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

// the inner stores over the inner counter are the column, with the fragment of the counter as a side condition over a
// fresh variable
lemma {:rw} invs_column_counter(ks: List<int>, hs: List<array<int, array<int, int>>>, Bs: List<Trace<array<int, array<int, int>>>>,
                                Js: List<Trace<int>>, Js2: List<Trace<int>>, A: array<int, array<int, int>>, n: int)
  requires invs(for ks, Js2 check k, J :: J == counter(0, 1, natural(n)))
  requires Js2 == Js
  ensures invs(for ks, hs, Bs, Js check k, h, B, J :: B == trace(h, for ⌊J⌋ do x, j :: x[j := x[j][k := A[k][j]]]))
    <==> invs(for ks, hs, Bs check k, h, B :: B == column(h, A, k, natural(n)))

// the final values of the inner traces, which are columns in the same iteration
lemma {:rw} invs_current_column(ks: List<int>, hs: List<array<int, array<int, int>>>, bs: List<array<int, array<int, int>>>,
                                Bs: List<Trace<array<int, array<int, int>>>>, Bs2: List<Trace<array<int, array<int, int>>>>,
                                A: array<int, array<int, int>>, n: int)
  requires invs(for ks, hs, Bs2 check k, h, B :: B == column(h, A, k, natural(n)))
  requires Bs2 == Bs
  ensures invs(for ks, bs, Bs check k, b, B :: b == current(B))
    <==> invs(for ks, hs, bs check k, h, b :: b == current(column(h, A, k, natural(n))))

// the results of the inner loop are a function F of the previous value and the iteration (transpose.dfy)
lemma {:rw} current_results_steps(x0: array<int, array<int, int>>, ks: List<int>, bs: List<array<int, array<int, int>>>,
                                  F: (array<int, array<int, int>>, int) -> array<int, array<int, int>>)
  requires invs(for ks, ⌊results(x0, ks, bs)⌋, bs check k, x, b :: b == F(x, k))
  ensures current(results(x0, ks, bs)) == current(trace(x0, for ks do x, k :: F(x, k)))

// m columns transpose the m x nn matrix (transpose.dfy)
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
