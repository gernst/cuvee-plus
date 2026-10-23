// ./Cuvee.sh -teq -prove examples/dafny/teq/init.dfy
// the initialization of the first n elements of the array a with the value v

method init(n: int, v: int) returns (a: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> a[k] == v
{
  var i: int;
  i := 0;
  while i < n
  {
    a[i] := v;
    i := i + 1;
  }
}
