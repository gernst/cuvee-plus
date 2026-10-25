// ./Cuvee.sh -prove examples/dafny/prove/slice_calls.dfy
// a call modifies the global variables of the modifies clause of its procedure, whose values after the call are not
// known: the test on h is decided after the call, the one on g is not

var g: int
var h: int

method set()
  modifies g

method calls() returns (r: int)
  modifies g, h
{
  g := 1;
  h := 2;
  set();
  if (h == 2) {
    r := 0;
  } else {
    r := 1;
  }
  if (g == 1) {
    r := r + 1;
  }
}
