// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_10.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_10.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: z counts up from 5000000 in the second half of x up to 10000000, and z == x is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (mono-crafted_9, _11 to _14 are
// variants)

method main() returns (result: int) {
  {
    var x: int, y: int, z: int;
    x := 0;
    y := 10000000;
    z := 5000000;
    while x < y {
      if x >= 5000000 {
        z := z + 1;
      }
      x := x + 1;
    }
    assert z == x;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
