// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/size.dfy
// sizes of renc, the predicate N of the versions: a display with two pairs, an overwrite, a set display with an
// insertion and a removal; each store or update bridges N in a side branch from the observed old membership
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
  m := m[1 := 11];
  z := |m|;
  s := {1, 2};
  s := s[3 := true];
  s := s[1 := false];
  y := |s|;
  assert z == 2 && y == 2;
}
