// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/remove.dfy
// the removal m - s of renc keeps the prophecy key of m and observes s there
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var m: map<int, int>;
  var b: bool;
  var x: int;
  tick := 0;
  m := map[];
  m := m[1 := 10];
  m := m[2 := 20];
  m := m - {1};
  b := 1 in m;
  x := m[2];
  assert !b && x == 20;
}
