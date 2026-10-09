// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_1.dfy
// SV-COMP loop-simple/nested_1.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_2 with other constants or assertions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6

method main() returns (result: int) {
  var N: int;
  var a: int;
  assume 0 < N;
  a := N;
  a := 0;
  while a < N {
    {}
    a := a + 1;
  }
  if a != N {
    assert false;
  }
  result := 1;
  return;
}
