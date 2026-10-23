// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/size_keys.dfy
// the keys of a map of renc share its version, hence its size
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var m: map<int, int>;
  var s: set<int>;
  var z: int;
  var y: int;
  tick := 0;
  m := map[1 := 10, 2 := 20];
  s := m.Keys;
  z := |m|;
  y := |s|;
  assert z == y && y == 2;
}
