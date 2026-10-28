// ./Cuvee.sh -teq -include teq:aggregation -entry fold -fallback examples/dafny/teq/fallback_fold.dfy
// a function defined with {:fold} whose result is no trace or list is unfolded, and its body lowered: the sum of the
// squares below n, the fold of the sum of a map over a counter, is the recursive sum over the entries of the map

function {:fold} squares_below(n: int): int
{
  sum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: k * k)))
}

method fold(m: int) returns (r: int)
  ensures 0 <= squares_below(m)
{
  r := 0;
}
