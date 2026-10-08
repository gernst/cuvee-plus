// ./Cuvee.sh examples/boogie/printing/statements.bpl
// types, specifications, assignments, calls, choices, else if, loops with their contracts, continue, which is
// part of the dialect, and termination measures, whose components are a single clause
type Stack<a>;
var m: [int, bool]int;
function empty<a>(): Stack<a>;
procedure p(x: int);
procedure q(x: int) returns (y: int);
procedure r(i: int, j: int) returns (x: int, y: int, a: [int]int)
  modifies m;
{
  assume x < y;
  assert x < y;
  havoc x, y;
  x, y := y, x;
  a := a[x := a[y]];
  call p(x);
  call y := q(x);
  if (*) { x := 0; } else { x := y; }
  while (true) { if (x < y) { break; } else if (y < x) { return; } }
  while (x < y) { continue; }
  while (x < y) invariant x <= y; modifies m; { }
  while (*) invariant x <= y; { x := y; }
  while (true) decreases x, y; { }
}
