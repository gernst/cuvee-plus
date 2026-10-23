// ./Cuvee.sh -quiet -implement examples/dafny/transform/invalid_implement_binder.dfy
// the applications of a function implemented by a method under a binder cannot be lifted into calls
function some(s: seq<int>): int

method {:implement some(s)} any(s: seq<int>) returns (x: int)
  ensures x in s

method m(t: seq<seq<int>>) returns (b: bool)
{
  b := forall s: seq<int> :: s in t ==> some(s) > 0;
}
