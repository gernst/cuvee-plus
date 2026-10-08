// ./Cuvee.sh examples/dafny/teq/copy.dfy
// the copy of the first n elements of an array a into the array b

method copy(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> b[k] == a[k]
{
  var i: int;
  i := 0;
  while i < n
  {
    b[i] := a[i];
    i := i + 1;
  }
}
