// ./Cuvee.sh -teq -entry main -prove examples/dafny/algorithms/nested_mult.dfy
// multiplication by repeated addition: the inner loop increments the outer variable n times; verified with the
// database alone, the inner loop a value of the outer update (Oct 23, 2026, formerly examples/dafny/state, whose
// version replaced the one here with the fragment lemmas of the former module nested, see doc/prove.md)

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
