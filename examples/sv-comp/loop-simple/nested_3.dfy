// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_3.dfy
// SV-COMP loop-simple/nested_3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_1 with other constants or assertions

method main() returns (result: int) {
  {
    var a: int;
    var b: int;
    var c: int;
    a := 6;
    b := 6;
    c := 6;
    a := 0;
    while a < 6 {
      b := 0;
      while b < 6 {
        c := 0;
        while c < 6 {
          {}
          c := c + 1;
        }
        b := b + 1;
      }
      a := a + 1;
    }
    if !(a == 6 && b == 6 && c == 6) {
      assert false;
    }
    result := 1;
    return;
  }
}
