// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/weak.dfy
// the size, the values, and the submap relation of renc depend on all keys and are constrained at the prophecy
// key only: sound, but weak, e.g. z >= 0 holds, z == 1 is answered incorrect although it is true
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies cnt
{
  var m: map<int, int>;
  var n: map<int, int>;
  var z: int;
  var t: set<int>;
  var b: bool;
  cnt := 0;
  m := map[];
  m := m[1 := 10];
  n := map[];
  z := |m|;
  t := m.Values;
  b := m <= n;
  assert z >= 0;
}
