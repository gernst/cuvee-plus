// the exchange of the first n elements of two arrays, element by element

method swap(a: array<int, int>, b: array<int, int>, n: int) returns (c: array<int, int>, d: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> c[k] == b[k] && d[k] == a[k]
{
  var i: int;
  var t: int;
  c := a;
  d := b;
  i := 0;
  while i < n
  {
    t := c[i];
    c[i] := d[i];
    d[i] := t;
    i := i + 1;
  }
}
