// ./Cuvee.sh -teq -entry main -prove examples/dafny/state/nested_counter.dfy
// examples/dafny/algorithms/nested_counter.dfy under -teq, without its lemmas (see doc/prove.md)

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
