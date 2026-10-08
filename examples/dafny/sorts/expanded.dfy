// ./Cuvee.sh -print smt2 examples/dafny/sorts/expanded.dfy
// defined sorts are expanded in expressions and programs by type checking, also in the types of variables,
// but not in the declarations, whose formal parameters keep them
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

lemma forall x: T :: x + 1 - 1 == x
