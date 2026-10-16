// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/transpose.dfy
// the transpose of an m x n matrix: nested loops that store A[i][j] at B[j][i]
//
// status (Oct 16, 2026): verified with -teq -prove; a wrong postcondition, B[j][i] == A[j][i], leaves a goal; the
// inner loop is a value of the outer update, folded into column(x, A, k, nn) over the numbers of inner iterations N?
// (a choice), which the constraints of the outer loop fix to natural(n) in every iteration, N? == ⌊consts(m', natural(n))⌋;
// current_transpose takes that equation as a side condition and reads the transposed element of the trace of the
// columns (the lemmas of the per-variable form for the fragments of the inner loop, the final values of the
// columns, and the outer trace as their results, are no longer needed)

// the inner loop: column k of the transpose, the stores of A[k][j] at B[j][k] for j below nn
function {:fold} column(B0: array<int, array<int, int>>, A: array<int, array<int, int>>, k: int, nn: Nat): Trace<array<int, array<int, int>>>
{
  trace(B0, for ⌊counter(0, 1, nn)⌋ do B, j :: B[j := B[j][k := A[k][j]]])
}

// m columns of nn rows each transpose the m x nn matrix, over the numbers of inner iterations as a choice ns that is
// nn in every iteration (ns == ⌊consts(m, nn)⌋ among the facts, with nn bound by it)
lemma {:rw} current_transpose(B0: array<int, array<int, int>>, A: array<int, array<int, int>>, m: Nat, nn: Nat,
                              ns: List<Nat>, i: int, j: int)
  requires ns == ⌊consts(m, nn)⌋
  ensures current(trace(B0, for ⌊counter(0, 1, m)⌋, ns do x, k, n :: current(column(x, A, k, n))))[j][i]
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
