// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/set_update.dfy
// updates s[x := d] of sets of renc, an insertion and a removal, which change the state at the prophecy element only;
// the display {1, 2} inserts 2 into {1}
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(x: int)
  modifies tick
{
  var s: set<int>;
  var b: bool;
  var c: bool;
  tick := 0;
  s := {1, 2};
  s := s[x := true];
  s := s[1 := false];
  b := x in s;
  c := 2 in s;
  assert (x != 1 ==> b) && c;
}
