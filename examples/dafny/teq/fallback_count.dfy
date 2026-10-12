// ./Cuvee.sh -teq -entry count -simplify -fallback examples/dafny/teq/fallback_count.dfy
// a combinator that is not equated to a variable, the flags of the positions counted, becomes a fresh function,
// whose arguments include the length n of the counter of its dependency

method count(a: array<int, int>, n: int) returns (c: int)
  requires 0 <= n
  ensures c <= n
{
  var i: int;
  i := 0;
  c := 0;
  while i < n {
    if a[i] < 0 {
      c := c + 1;
    }
    i := i + 1;
  }
}
