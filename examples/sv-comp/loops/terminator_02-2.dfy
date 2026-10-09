// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/terminator_02-2.dfy
// SV-COMP loops/terminator_02-2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: x is incremented, or x and z are decremented, nondeterministically, while x < 100 and z > 100, and
// the negation of the test is checked at the end
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100

method main() returns (result: int) {
  var N: int;
  var tmp₁: int, tmp₂: int, tmp₃: bool;
  assume 0 < N;
  {
    var x: int, z: int;
    tmp₁ := *;
    x := tmp₁;
    tmp₂ := *;
    z := tmp₂;
    if !(x > -N) {
      result := 0;
      return;
    }
    if !(x < 200) {
      result := 0;
      return;
    }
    if !(z > N) {
      result := 0;
      return;
    }
    if !(z < 200) {
      result := 0;
      return;
    }
    while x < N && z > N {
      var tmp: bool;
      tmp₃ := *;
      tmp := tmp₃;
      if tmp {
        x := x + 1;
      } else {
        x := x - 1;
        z := z - 1;
      }
    }
    assert x >= N || z <= N;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
