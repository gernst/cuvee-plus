// ./Cuvee.sh -teq -prove examples/dafny/state/swap.dfy
// the exchange of the first n elements of two arrays, element by element (examples/dafny/teq/swap.dfy), by one trace:
// the arrays and the index form one cycle, whose per-variable traces are projections (see ideas/state-trace.md)

method swap(a: array<int, int>, b: array<int, int>, n: int) returns (a_: array<int, int>, b_: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> a_[k] == b[k] && b_[k] == a[k]
{
  var i: int;
  var t: int;
  a_ := a;
  b_ := b;
  i := 0;
  while i < n
  {
    t := a_[i];
    a_[i] := b_[i];
    b_[i] := t;
    i := i + 1;
  }
}
