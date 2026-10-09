// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_6.dfy
// SV-COMP ReachSafety-Loops/loop-simple/nested_6.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested_1 with other constants or assertions

method main() returns (result: int) {
  {
    var a: int;
    var b: int;
    var c: int;
    var d: int;
    var e: int;
    var f: int;
    a := 6;
    b := 6;
    c := 6;
    d := 6;
    e := 6;
    f := 6;
    a := 0;
    while a < 6 {
      b := 0;
      while b < 6 {
        c := 0;
        while c < 6 {
          d := 0;
          while d < 6 {
            e := 0;
            while e < 6 {
              f := 0;
              while f < 6 {
                {}
                f := f + 1;
              }
              e := e + 1;
            }
            d := d + 1;
          }
          c := c + 1;
        }
        b := b + 1;
      }
      a := a + 1;
    }
    if !(a == 6 && b == 6 && c == 6 && d == 6 && e == 6 && f == 6) {
      assert false;
    }
    result := 1;
    return;
  }
}
