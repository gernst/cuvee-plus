// ./Cuvee.sh -prove examples/dafny/prove/slice_loops.dfy
// a loop starts from fresh values of the variables that it modifies, constrained by its invariants, the facts from
// before the loop hold in it and after it: after the first loop, 0 <= x holds by the invariant and the test of the if
// is decided; y is not modified, hence y == 5 holds after it; the second loop is not entered, but its invariant is
// checked where the loop was, as an assertion; the statements after assume false are unreachable and dropped

method loops(a: int) returns (r: int)
{
  var x: int;
  var y: int;
  var i: int;
  x := 0;
  y := 5;
  i := 0;
  while (i < a)
    invariant 0 <= x
  {
    x := x + 1;
    i := i + 1;
  }
  if (0 <= x && y == 5) {
    r := x;
  } else {
    r := -1;
  }
  while (y < 5)
    invariant 0 <= y
  {
    y := y + 1;
  }
  assume false;
  r := 0;
}
