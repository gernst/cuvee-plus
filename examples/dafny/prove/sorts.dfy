// ./Cuvee.sh -prove examples/dafny/prove/sorts.dfy
// arithmetic on defined sorts is normalized, which was a type mismatch before, the lemma vanishes
type T = int
var count: T

method incr(y: T) returns (z: T)
  modifies count
  ensures z == y + 1 && count == old(count) + 1
{
  z := y + 1;
  count := count + 1;
}

method twice(a: T) returns (b: T)
  modifies count
  ensures b == a + 2 && count == old(count) + 2
{
  var c: T;
  c := a;
  b := incr(c);
  b := incr(b);
}

lemma lemma_1(x: T)
  ensures x + 1 - 1 == x
{}
