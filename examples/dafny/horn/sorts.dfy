// ./Cuvee.sh -chc -entry main examples/dafny/horn/sorts.dfy
// expected: valid
// the predicates of the procedures have the expanded types of the formal parameters and global variables
type T = int
var count: T

method incr(y: T) returns (z: T)
  modifies count
{
  z := y + 1;
  count := count + 1;
}

method main(a: T) returns (b: T)
  modifies count
{
  var c: T;
  c := count;
  b := incr(a);
  assert b == a + 1 && count == c + 1;
}
