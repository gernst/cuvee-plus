// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_sets.dfy
// sets by the encoding of renc: 1 is not in {1, 2} - {1}
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies cnt
{
  var s: set<int>;
  var t: set<int>;
  var b: bool;
  var c: bool;
  cnt := 0;
  s := {1, 2};
  t := s - {1};
  b := 1 in t;
  c := 2 in t;
  assert b;
}
