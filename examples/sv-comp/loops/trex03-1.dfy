// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/trex03-1.dfy
// SV-COMP ReachSafety-Loops/loops/trex03-1.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of trex01-1 with other constants or assertions; checks x1==0 && x2==0 && x3==0

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: bool;
  var tmp₅: bool;
  {
    var x1: int;
    var x2: int;
    var x3: int;
    var d1: int;
    var d2: int;
    var d3: int;
    var c1: bool;
    var c2: bool;
    tmp₁ := *;
    assume 0 <= tmp₁;
    x1 := tmp₁;
    tmp₂ := *;
    assume 0 <= tmp₂;
    x2 := tmp₂;
    tmp₃ := *;
    assume 0 <= tmp₃;
    x3 := tmp₃;
    d1 := 1;
    d2 := 1;
    d3 := 1;
    tmp₄ := *;
    c1 := tmp₄;
    tmp₅ := *;
    c2 := tmp₅;
    while x1 > 0 && x2 > 0 && x3 > 0 {
      if c1 {
        x1 := x1 - d1;
      } else if c2 {
        x2 := x2 - d2;
      } else {
        x3 := x3 - d3;
      }
      c1 := *;
      c2 := *;
    }
    assert x1 == 0 && x2 == 0 && x3 == 0;
    result := 0;
    return;
  }
}
