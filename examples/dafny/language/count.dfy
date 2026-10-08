// ./Cuvee.sh examples/dafny/language/count.dfy
// a counter, whose loop is summarized by a trace equation system with -teq

method count(n: int) returns (i: int)
  requires 0 <= n
  ensures i == n
{
  i := 0;
  while i < n
  {
    i := i + 1;
  }
}
