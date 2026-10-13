// ./Cuvee.sh -teq -entry fib -prove -fallback examples/dafny/teq/fallback_accumulators.dfy
// the fallback encoding of a trace of several accumulators, the cycle of a and b: one function per accumulator, whose
// results read the entries of both at the previous position, and the components current(S).i at the last position

method fib(n: int) returns (a: int)
  requires 0 <= n
  ensures 0 <= a
{
  var b: int;
  var t: int;
  var i: int;
  a := 0;
  b := 1;
  i := 0;
  while i < n {
    t := a + b;
    a := b;
    b := t;
    i := i + 1;
  }
}
