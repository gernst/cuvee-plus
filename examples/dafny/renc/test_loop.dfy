// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/test_loop.dfy
// a loop stores at the even keys, a test after it does not find an odd key
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int, k: int)
  modifies tick
{
  var m: map<int, int>;
  var i: int;
  var b: bool;
  tick := 0;
  m := map[];
  i := 0;
  while i < n
  {
    m := m[2 * i := i];
    i := i + 1;
  }
  b := 2 * k + 1 in m;
  assert !b;
}
