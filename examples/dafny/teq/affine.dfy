// ./Cuvee.sh -teq -entry affine -prove examples/dafny/teq/affine.dfy
// an update of each entry that reads the entry itself, in the context c * b[i] + i, which reads the initial value,
// since the keys are distinct (the higher-order lemma on distinct keys in teq.dfy)
method affine(a: array<int, int>, n: int, c: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> b[k] == c * a[k] + k
{
  var i: int;
  b := a;
  i := 0;
  while i < n
  {
    b[i] := c * b[i] + i;
    i := i + 1;
  }
}
