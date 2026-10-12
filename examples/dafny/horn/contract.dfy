// ./Cuvee.sh -chc -entry main examples/dafny/horn/contract.dfy
// expected: valid
// a polymorphic method without body is used by its contract, instantiated for the monomorphic caller

datatype pair<a> = pair(fst: a, snd: a)

method swap<a>(p: pair<a>) returns (q: pair<a>)
  ensures q.fst == p.snd && q.snd == p.fst

method main(x: int, y: int)
{
  var p: pair<int>;
  p := swap(pair(x, y));
  assert p.fst == y;
}
