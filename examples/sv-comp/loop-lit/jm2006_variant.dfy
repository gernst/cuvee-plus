// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/jm2006_variant.dfy
// SV-COMP ReachSafety-Loops/loop-lit/jm2006_variant.yml (expected: safe), translated from the C program by hand: x
// counts down from i to 0, y by 2 from j, z up from 0; if i == j, then y == -z is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var j: int;
  var x: int;
  var y: int;
  var z: int;
  i := *;
  j := *;
  if !(i >= 0 && i <= 1000000) {
    return;
  }
  if !(j >= 0) {
    return;
  }
  x := i;
  y := j;
  z := 0;
  while x != 0 {
    x := x - 1;
    y := y - 2;
    z := z + 1;
  }
  if i == j {
    assert y == -z;
  }
}

// remaining goals of -teq -simplify:
// none
