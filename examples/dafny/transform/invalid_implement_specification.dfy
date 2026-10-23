// ./Cuvee.sh -quiet -implement examples/dafny/transform/invalid_implement_specification.dfy
// a function implemented by a method is nondeterministic, hence it must not occur in specifications
function some(s: seq<int>): int

method {:implement some(s)} any(s: seq<int>) returns (x: int)
  ensures x in s

method m(s: seq<int>) returns (x: int)
  ensures x == some(s)
{
  x := some(s);
}
