// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/state/row_sums.dfy
// examples/dafny/algorithms/row_sums.dfy under -teq, without its lemmas (see ideas/state-trace.md)

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
