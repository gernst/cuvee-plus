// ./Cuvee.sh -instrument examples/dafny/transform/instrument.dfy
// -instrument inlines the bodies of the implementations by methods instead of calling them: a block whose locals are
// the formal parameters renamed apart (x and y of m), with the types instantiated (a by int), which asserts the
// precondition, keeps the global variables for old, and assigns the output to the result; the inlined methods are
// dropped, a method without body (any) is called
var count: int

function first<a>(x: a, y: a): a
function some(s: seq<int>): int

method {:implement first(x, y)} pick<a>(x: a, y: a) returns (z: a)
  modifies count
{
  count := count + 1;
  assert count == old(count) + 1;
  z := *;
  assume z == x || z == y;
}

method {:implement some(s)} any(s: seq<int>) returns (x: int)
  requires |s| > 0
  ensures x in s

function get(s: seq<int>, i: int): int
method {:implement get(s, i)} at(s: seq<int>, i: int) returns (x: int)
  requires 0 <= i < |s|
{
  x := s[i];
}

method m(x: int, y: int, s: seq<int>) returns (r: int)
  modifies count
  requires 0 < |s|
{
  r := first(y, x) + some(s) + get(s, 0);
}
