// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/terminator_03-2.dfy
// SV-COMP loops/terminator_03-2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: x grows by y > 0 until it reaches 100, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100

method main() returns (result: int) {
  var N: int;
  var tmp₁: int, tmp₂: int;
  var x: int, y: int;
  assume 0 < N;
  tmp₁ := *;
  x := tmp₁;
  tmp₂ := *;
  y := tmp₂;
  if !(y <= 1000000) {
    result := 0;
    return;
  }
  if y > 0 {
    while x < N {
      x := x + y;
    }
  }
  assert y <= 0 || y > 0 && x >= N;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
