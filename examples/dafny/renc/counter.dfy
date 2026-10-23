// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/counter.dfy
// a loop that reads and stores the same key, a counter in the map: the observations in the loop are
// numbered by tick, the context (n, i, x) tells their executions apart
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int)
  modifies tick
  requires 0 <= n
{
  var m: map<int, int>;
  var i: int;
  var x: int;
  tick := 0;
  m := map[];
  m := m[0 := 0];
  i := 0;
  while i < n
  {
    x := m[0];
    m := m[0 := x + 1];
    i := i + 1;
  }
  x := m[0];
  assert x == n;
}
