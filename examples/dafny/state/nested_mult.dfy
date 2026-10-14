// ./Cuvee.sh -teq -entry main -prove examples/dafny/state/nested_mult.dfy
// examples/dafny/algorithms/nested_mult.dfy under -teq, without its lemmas (see doc/prove.md)

method main(m: int, n: int) returns (r: int)
  requires 0 <= m && 0 <= n
  ensures r == m * n
{
  var i: int;
  var j: int;
  r := 0;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      r := r + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
