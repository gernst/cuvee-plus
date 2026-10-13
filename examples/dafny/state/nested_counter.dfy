// ./Cuvee.sh -teq-state -entry main -prove examples/dafny/state/nested_counter.dfy
// examples/dafny/algorithms/nested_counter.dfy with state traces, without its lemmas (see ideas/state-trace.md)

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
