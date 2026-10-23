// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/remove.dfy
// the removal m - s of renc keeps the prophecy key of m and observes s there
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies cnt
{
  var m: map<int, int>;
  var b: bool;
  var x: int;
  cnt := 0;
  m := map[];
  m := m[1 := 10];
  m := m[2 := 20];
  m := m - {1};
  b := 1 in m;
  x := m[2];
  assert !b && x == 20;
}
