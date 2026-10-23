// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 examples/dafny/transform/invalid_implement_renc.dfy
// maps implemented by the heap encoding Enc_R (resources/cuvee/implement/renc.dfy): -instrument inlines the test and
// the read into the program, whose Horn clauses are monomorphic, z3 infers the predicates K and R of the answers to
// the test and of the read values, the key 1 is in the map, but its read does not see 20
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
  b := 1 in m;
  x := m[1];
  assert b && x == 20;
}
