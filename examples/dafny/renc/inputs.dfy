// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/inputs.dfy
// keys and values given by the inputs: the reads of renc receive the context of the client, here (i, j, a, b, x),
// which tells the executions apart, such that z3 infers R(ctx, c, v) with v == a; without the context, the read
// would see the values of all inputs
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(i: int, j: int, a: int, b: int)
  modifies tick
  requires i != j
{
  var m: map<int, int>;
  var x: int;
  tick := 0;
  m := map[];
  m := m[i := a];
  m := m[j := b];
  x := m[i];
  assert x == a;
}
