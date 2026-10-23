// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/sets.dfy
// sets by the encoding of renc: the display {1, 2} is the union of singletons, the difference keeps the prophecy
// element of s and observes {1} there, tests are observations with the predicate S
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main()
  modifies tick
{
  var s: set<int>;
  var t: set<int>;
  var b: bool;
  var c: bool;
  tick := 0;
  s := {1, 2};
  t := s - {1};
  b := 1 in t;
  c := 2 in t;
  assert !b && c;
}
