// ./Cuvee.sh -instrument examples/boogie/transform/instrument.bpl
// -instrument: as -implement (implement.bpl), except that the procedure with a body (succ) is inlined
// instead of called, as a block whose locals are its formal parameters renamed apart, and dropped; the one with
// a contract only (between) is called
function twice(x: int): int;
function {:implement twice(x)} double(x: int): int { 2 * x }
function some(lo: int, hi: int): int;
procedure {:implement some(lo, hi)} between(lo: int, hi: int) returns (x: int);
  requires lo <= hi;
  ensures lo <= x && x <= hi;
function other(y: int): int;
procedure {:implement other(y)} succ(y: int) returns (z: int)
{
  z := y + 1;
}
procedure main(n: int) returns (r: int)
{
  r := twice(n);
  r := some(0, r) + other(r);
}
