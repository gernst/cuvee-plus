// ./Cuvee.sh -implement examples/dafny/transform/implement_method.dfy
// a function implemented by a method, which may choose its result nondeterministically: the applications in the
// expressions that the program executes become calls, in the order of evaluation, whose results are fresh locals,
// the right operand of && only where it is evaluated, the calls of a loop guard before each test
function some(s: seq<int>): int

method {:implement some(s)} any(s: seq<int>) returns (x: int)
  requires |s| > 0
  ensures x in s

method m(s: seq<int>) returns (x: int, b: bool)
  requires |s| > 0
{
  x := some(s) + some(s);
  if some(s) > 0 {
    b := true;
  } else {
    b := false;
  }
  b := b && some(s) == x;
  while b && some(s) < x {
    x := x - 1;
  }
}
