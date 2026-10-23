// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_absent.dfy
// the read m[2] of a key that is not in the map has an arbitrary value, which its prophecy run asserts, such
// that the solver cannot block all runs there; m[1] is 10, not 20
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var m: map<int, int>;
  var x: int;
  var y: int;
  tick := 0;
  m := map[];
  m := m[1 := 10];
  x := m[1];
  y := m[2];
  assert x == 20;
}
