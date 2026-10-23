// ./Cuvee.sh -implement examples/boogie/transform/implement.bpl
// implementations named by {:implement pattern}, the implemented function applied to the inputs: a function replaces
// its function everywhere (twice by double), a procedure, with a contract or a body, replaces the applications in the
// expressions that programs execute by calls (some by between, other by succ)
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
