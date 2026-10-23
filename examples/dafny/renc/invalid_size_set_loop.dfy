// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_size_set_loop.dfy
// a loop that inserts n new elements: the size is n, not n - 1
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int)
  modifies tick
  requires 0 <= n
{
  var s: set<int>;
  var i: int;
  var z: int;
  tick := 0;
  s := {};
  i := 0;
  while i < n
  {
    s := s[2 * i := true];
    i := i + 1;
  }
  z := |s|;
  assert z == n - 1;
}
