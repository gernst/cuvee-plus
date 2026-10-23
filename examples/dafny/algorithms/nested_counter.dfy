// ./Cuvee.sh -teq -entry main -prove examples/dafny/algorithms/nested_counter.dfy
// the simplest nested loop: the inner loop counts to n and has no effect on the outer variable; verified with the
// database alone (Oct 23, 2026, formerly examples/dafny/state, see doc/prove.md)

method main(m: int, n: int) returns (i: int)
  requires 0 <= m && 0 <= n
  ensures i == m
{
  var j: int;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      j := j + 1;
    }
    i := i + 1;
  }
}
