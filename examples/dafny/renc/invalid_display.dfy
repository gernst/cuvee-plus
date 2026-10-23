// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_display.dfy
// the display map[1 := 10, 2 := 20]: m[1] is 10, not 20
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var m: map<int, int>;
  var x: int;
  var y: int;
  tick := 0;
  m := map[1 := 10, 2 := 20];
  x := m[1];
  y := m[2];
  assert x == 20;
}
