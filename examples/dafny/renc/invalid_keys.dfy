// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_keys.dfy
// the keys of a map of renc: 2 is not a key
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies cnt
{
  var m: map<int, int>;
  var s: set<int>;
  var b: bool;
  var c: bool;
  cnt := 0;
  m := map[];
  m := m[1 := 10];
  s := m.Keys;
  b := 1 in s;
  c := 2 in s;
  assert c;
}
