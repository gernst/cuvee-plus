// ./Cuvee.sh examples/dafny/parsing/datatypes.dfy
// annotated constructors, testers, the keys of maps, and members, inside of which the fields, functions, and methods
// of the type are accessible without this
datatype list<a> = nil | cons(head: a, tail: list<a>)
function annotation(xs: list<int>): bool { xs != nil as list<int> }
function tester(xs: list<int>): bool { xs.cons? && !xs.nil? }
function keys(m: map<int, bool>): set<int> { m.Keys }
datatype pair = pair(fst: int, snd: int)
{
  function sum(): int { fst + snd }
  function twice(): int { sum() + this.sum() }
  method get() returns (x: int) { x := fst; }
  method get2() returns (y: int) { y := get(); }
}
