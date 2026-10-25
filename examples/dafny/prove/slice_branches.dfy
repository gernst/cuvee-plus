// ./Cuvee.sh -prove examples/dafny/prove/slice_branches.dfy
// procedures are simplified by symbolic execution (Slice): the second test is false, since the value of x after the
// first if is ite(a < 0, -a, a), whose cases are decided each under its test; the decided if is dropped, the other
// statements stay as written, where expressions are written back over the variables that hold their values: x := -x,
// and r := x, since y is 0

method branches(a: int) returns (r: int)
{
  var x: int;
  var y: int;
  x := a;
  y := 0;
  if (x < 0) {
    x := -x;
  }
  if (x < 0) {
    y := 1;
  }
  r := x + y;
}
