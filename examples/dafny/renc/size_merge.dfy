// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/size_merge.dfy
// the size after a merge is only bounded, by max(|m|, |n|) and |m| + |n|, after which stores count exactly:
// between 2 and 3 here, although it is 3
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var m: map<int, int>;
  var n: map<int, int>;
  var z: int;
  tick := 0;
  m := map[1 := 10];
  n := map[2 := 20];
  m := m + n;
  m := m[3 := 30];
  z := |m|;
  assert 2 <= z <= 3;
}
