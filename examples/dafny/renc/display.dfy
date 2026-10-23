// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/display.dfy
// the display map[1 := 10] is the singleton of renc, whose prophecy key holds the value if it is 1
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies cnt
{
  var m: map<int, int>;
  var x: int;
  cnt := 0;
  m := map[1 := 10];
  x := m[1];
  assert x == 10;
}
