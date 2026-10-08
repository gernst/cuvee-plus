// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/invalid_seq.dfy
// expected: invalid
// the element is at the front, not at the back

method cons(s: seq<int>, x: int) returns (t: seq<int>)
  requires 0 < |s|
  ensures t[|t| - 1] == x
{
  t := [x] + s;
}
