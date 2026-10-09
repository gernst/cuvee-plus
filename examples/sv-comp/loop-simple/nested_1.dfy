// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_1.dfy
// SV-COMP ReachSafety-Loops/loop-simple/nested_1.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_2 with other constants or assertions

method main() returns (result: int) {
  {
    var a: int;
    a := 6;
    a := 0;
    while a < 6 {
      {}
      a := a + 1;
    }
    if a != 6 {
      assert false;
    }
    result := 1;
    return;
  }
}
