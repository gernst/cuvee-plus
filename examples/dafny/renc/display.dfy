// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/display.dfy
// the display map[1 := 10, 2 := 20] stores 2 := 20 into the singleton map[1 := 10] (Dafny frontend), both exact in renc
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
  assert x == 10 && y == 20;
}
