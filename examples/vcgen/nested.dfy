// expected: valid
// nested loops, loop body with local variable

method mult(a: int, b: int) returns (r: int)
  requires 0 <= a && 0 <= b
  ensures r == a * b
{
  var i: int;
  i := 0;
  r := 0;
  while i < a
    invariant 0 <= i && i <= a
    invariant r == i * b
  {
    var j: int;
    j := 0;
    while j < b
      invariant 0 <= j && j <= b
      invariant r == i * b + j
    {
      r := r + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
