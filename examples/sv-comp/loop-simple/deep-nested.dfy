// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/deep-nested.dfy
// SV-COMP ReachSafety-Loops/loop-simple/deep-nested.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder
// note: the concrete loop bounds are symbolic, arbitrary positive values: uint32_max for 4294967295

method main() returns (result: int) {
  {
    var a: int;
    var b: int;
    var c: int;
    var d: int;
    var e: int;
    var uint32_max: int;
    uint32_max := *;
    assume 0 < uint32_max;
    a := 0;
    while a < uint32_max - 1 {
      b := 0;
      while b < uint32_max - 1 {
        c := 0;
        while c < uint32_max - 1 {
          d := 0;
          while d < uint32_max - 1 {
            e := 0;
            while e < uint32_max - 1 {
              if a == b == c == d == e == uint32_max - 2 {
                assert false;
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
    result := 0;
    return;
  }
}
