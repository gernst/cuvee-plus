// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_merge.dfy
// after a merge, the observations of the merge are numbered alike in all runs (two, also if the key is not
// in n), such that the reads after it find the runs that assert their values; m[1] is 10, not 20
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies cnt
{
  var m: map<int, int>;
  var n: map<int, int>;
  var x: int;
  var y: int;
  cnt := 0;
  m := map[];
  m := m[1 := 10];
  n := map[];
  n := n[2 := 20];
  m := m + n;
  x := m[1];
  y := m[2];
  assert x == 20;
}
