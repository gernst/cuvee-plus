// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/invalid_size_overwrite_loop.dfy
// a loop that overwrites the same key: the size is 1, not n
// (tick := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int)
  modifies tick
  requires 0 < n
{
  var m: map<int, int>;
  var i: int;
  var z: int;
  tick := 0;
  m := map[];
  i := 0;
  while i < n
  {
    m := m[0 := i];
    i := i + 1;
  }
  z := |m|;
  assert z == n;
}
