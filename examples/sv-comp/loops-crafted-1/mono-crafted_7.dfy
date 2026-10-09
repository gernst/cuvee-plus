// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_7.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_7.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: as mono-crafted_3 from 50000, with x and y stepping down by 2, and z == x is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  {
    var x: int, y: int, z: int;
    x := 0;
    y := 50000;
    z := 0;
    x := 0;
    while x < 1000000 {
      if x < 50000 {
        x := x + 1;
      } else {
        x := x + 1;
        y := y + 1;
      }
    }
    while y > 0 {
      y := y - 2;
      x := x - 2;
    }
    assert z == x;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
