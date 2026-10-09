// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_1b.dfy
// SV-COMP loop-simple/nested_1b.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder

method main() returns (result: int) {
  var a: int;
  a := 6;
  a := 0;
  while a < 6 {
    {}
    a := a + 1;
  }
  if a == 6 {
    assert false;
  }
  result := 1;
  return;
}
