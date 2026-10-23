// ./Cuvee.sh -teq -entry main -prove examples/dafny/algorithms/nested_sum.dfy
// the result of the inner loop is used once per outer iteration, with the inner loop as a value of the outer update;
// verified with the database alone (Oct 23, 2026, formerly examples/dafny/state, whose version replaced the one here
// with the fragment lemmas of the former module nested, see doc/prove.md)

method main(m: int, n: int) returns (c: int)
  requires 0 <= m && 0 <= n
  ensures c == m * n
{
  var i: int;
  var j: int;
  c := 0;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      j := j + 1;
    }
    c := c + j;
    i := i + 1;
  }
}
