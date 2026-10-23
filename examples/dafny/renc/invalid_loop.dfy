// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_loop.dfy
// a loop fills the map, the read after it sees 2 * k, not 2 * k + 1
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int, k: int)
  modifies tick
  requires 0 <= k < n
{
  var m: map<int, int>;
  var i: int;
  var x: int;
  tick := 0;
  m := map[];
  i := 0;
  while i < n
  {
    m := m[i := 2 * i];
    i := i + 1;
  }
  x := m[k];
  assert x == 2 * k + 1;
}
