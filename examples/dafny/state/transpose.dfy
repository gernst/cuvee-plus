// ./Cuvee.sh -teq -entry main -prove examples/dafny/state/transpose.dfy
// examples/dafny/algorithms/transpose.dfy under -teq and one summary lemma on the nested fold, in place of its
// folds results and column and four lemmas on fragments (see ideas/state-trace.md)

// the transpose: the outer loop over the columns k of A, the inner over the rows ki of B, which stores A[k][ki] at
// B[ki][k]; the inner number of iterations is stated as natural(n), since the goal binds it to a choice whose
// values are natural(n) (consts_choice), which the matcher follows through its definition
lemma {:rw} current_transpose(B0: array<int, array<int, int>>, A: array<int, array<int, int>>, m: int, n: int, i: int, j: int)
  requires 0 <= i < m && 0 <= j < n
  ensures current(trace(B0, for ⌊counter(0, 1, natural(m))⌋ do B, k ::
      current(trace(B, for ⌊counter(0, 1, natural(n))⌋ do Bi, ki :: Bi[ki := Bi[ki][k := A[k][ki]]]))))[j][i]
    == A[i][j]

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
