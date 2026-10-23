// ./Cuvee.sh -include implement:renc -instrument -chc -entry main -monomorph -flat -z3 -timeout 30000 examples/dafny/renc/set_loop.dfy
// a loop adds the even numbers below 2 * n to a set of renc, a test after it finds 2 * k
// (cnt := 0 by hand: the start of the numbering of the observations is arbitrary otherwise)
method main(n: int, k: int)
  modifies cnt
  requires 0 <= k < n
{
  var s: set<int>;
  var i: int;
  var b: bool;
  cnt := 0;
  s := {};
  i := 0;
  while i < n
  {
    s := s + {2 * i};
    i := i + 1;
  }
  b := 2 * k in s;
  assert b;
}
