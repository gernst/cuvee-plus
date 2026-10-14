// ./Cuvee.sh -teq -prove examples/dafny/state/counter.dfy
// examples/dafny/teq/counter.dfy under -teq (see doc/prove.md)
// a counter that runs up to n, which it reaches at the end

method counter(n: int) returns (i: int)
  requires 0 <= n
  ensures i == n
{
  i := 0;
  while i < n
  {
    i := i + 1;
  }
}
