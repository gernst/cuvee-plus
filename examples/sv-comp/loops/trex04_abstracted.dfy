// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/trex04_abstracted.dfy
// SV-COMP loops/trex04_abstracted.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks x<=0

method foo() {
  var tmp₁: bool;
  var tmp₂: bool;
  {
    var y: int;
    var c1: bool;
    var c2: bool;
    y := 0;
    tmp₁ := *;
    c1 := tmp₁;
    tmp₂ := *;
    c2 := tmp₂;
    if c1 {
      y := y + 1;
    }
    if c2 {
      y := y - 1;
    } else {
      y := y + 10;
    }
  }
}

method main() returns (result: int) {
  var tmp₃: int;
  var tmp₄: bool;
  var tmp₅: bool;
  {
    var d: int;
    var x: int;
    var c1: bool;
    var c2: bool;
    d := 1;
    tmp₃ := *;
    x := tmp₃;
    if !(x <= 1000000 && x >= -1000000) {
      result := 0;
      return;
    }
    tmp₄ := *;
    c1 := tmp₄;
    tmp₅ := *;
    c2 := tmp₅;
    if c1 {
      d := d - 1;
    }
    if c2 {
      foo();
    }
    c1 := *;
    c2 := *;
    if c1 {
      foo();
    }
    if c2 {
      d := d - 1;
    }
    if x > 0 {
      x := *;
    }
    if x > 0 {
      assume false;
    }
    assert x <= 0;
  }
}
