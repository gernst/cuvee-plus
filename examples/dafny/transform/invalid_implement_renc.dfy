// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -flat -monomorph -z3 examples/dafny/transform/invalid_implement_renc.dfy
// maps implemented by the heap encoding Enc_R (resources/cuvee/implement/renc.dfy): -instrument inlines the reads
// into the program, whose Horn clauses are monomorphic, z3 infers the predicate R of the read values, the read of
// the key 1 does not see 20
method main()
{
  var m: map<int, int>;
  var x: int;
  m := map[];
  m := m[1 := 10];
  m := m[2 := 20];
  x := m[1];
  assert x == 20;
}
