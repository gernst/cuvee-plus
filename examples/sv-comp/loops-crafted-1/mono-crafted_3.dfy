// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_3.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts to 1000000, y counts along from 500000 in the second half, then x counts down and
// z up while y steps down by 2, and x == z is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  {
    var x: int, y: int, z: int;
    x := 0;
    y := 500000;
    z := 0;
    x := 0;
    while x < 1000000 {
      if x < 500000 {
        x := x + 1;
      } else {
        x := x + 1;
        y := y + 1;
      }
    }
    while y > 0 {
      x := x - 1;
      z := z + 1;
      y := y - 2;
    }
    assert x == z;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
