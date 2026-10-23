// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/merge.dfy
// the merge m + n of renc keeps the prophecy key of m and observes n there, a test and a read, whose context
// includes the observed key: the key 1 of n wins, the key 2 comes from n
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var m: map<int, int>;
  var n: map<int, int>;
  var r: map<int, int>;
  var x: int;
  var y: int;
  tick := 0;
  m := map[];
  m := m[1 := 10];
  n := map[];
  n := n[1 := 11];
  n := n[2 := 20];
  r := m + n;
  x := r[1];
  y := r[2];
  assert x == 11 && y == 20;
}
