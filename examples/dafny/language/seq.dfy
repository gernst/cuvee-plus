// ./Cuvee.sh examples/dafny/language/seq.dfy
// updates of sequences s[i := v] are seq.update in cvc5, which z3 does not support,
// verified with -verify -cvc5

method swap(s: seq<int>) returns (t: seq<int>)
  requires |s| == 2
  ensures t == [s[1], s[0]]
{
  t := s[0 := s[1]][1 := s[0]];
}
