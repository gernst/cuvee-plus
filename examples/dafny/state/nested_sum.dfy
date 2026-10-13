// ./Cuvee.sh -teq-state -entry main -prove examples/dafny/state/nested_sum.dfy
// the result of the inner loop is used once per outer iteration (examples/dafny/algorithms/nested_sum.dfy), with state
// traces and the inner loop as a value of the outer update, without the fragment lemmas (see ideas/state-trace.md)

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
