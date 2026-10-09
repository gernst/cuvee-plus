// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_4.dfy
// SV-COMP ReachSafety-Loops/loop-simple/nested_4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_1 with other constants or assertions

method main() returns (result: int) {
  {
    var a: int;
    var b: int;
    var c: int;
    var d: int;
    a := 6;
    b := 6;
    c := 6;
    d := 6;
    a := 0;
    while a < 6 {
      b := 0;
      while b < 6 {
        c := 0;
        while c < 6 {
          d := 0;
          while d < 6 {
            {}
            d := d + 1;
          }
          c := c + 1;
        }
        b := b + 1;
      }
      a := a + 1;
    }
    if !(a == 6 && b == 6 && c == 6 && d == 6) {
      assert false;
    }
    result := 1;
    return;
  }
}
