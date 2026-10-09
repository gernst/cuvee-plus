// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invariants/eq2.dfy
// SV-COMP ReachSafety-Loops/loop-invariants/eq2.yml (expected: safe), translated from the C program by hand: y and
// z start at w + 1 and are incremented together, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var w: int;
  var x: int;
  var y: int;
  var z: int;
  var b: int;
  havoc w;
  x := w;
  y := w + 1;
  z := x + 1;
  havoc b;
  while b != 0 {
    y := y + 1;
    z := z + 1;
    havoc b;
  }
  assert y == z;
}

// remaining goals of -teq -simplify:
// none
