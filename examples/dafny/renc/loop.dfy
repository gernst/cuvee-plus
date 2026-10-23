// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/loop.dfy
// a loop fills the map, the read after it sees the value stored for k: z3 infers the invariant of the
// state of the encoding (the prophecy key holds 2 * key if it is below i) and R
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int, k: int)
  modifies cnt
  requires 0 <= k < n
{
  var m: map<int, int>;
  var i: int;
  var x: int;
  cnt := 0;
  m := map[];
  i := 0;
  while i < n
  {
    m := m[i := 2 * i];
    i := i + 1;
  }
  x := m[k];
  assert x == 2 * k;
}
