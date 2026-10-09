// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/in-de61.dfy
// SV-COMP loops-crafted-1/in-de61.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of in-de20 with other constants or assertions; checks z==n

method main() returns (result: int) {
  var tmp₁: int;
  {
    var n: int;
    var x: int;
    var y: int;
    var z: int;
    tmp₁ := *;
    assume 0 <= tmp₁;
    n := tmp₁;
    x := n;
    y := 0;
    while x > 0 {
      x := x - 1;
      y := y + 1;
    }
    z := y;
    while z > 0 {
      x := x + 1;
      z := z - 1;
    }
    while y > 0 {
      y := y - 1;
      z := z + 1;
    }
    while x > 0 {
      x := x - 1;
      y := y + 1;
    }
    while z > 0 {
      x := x + 1;
      z := z - 1;
    }
    while y > 0 {
      y := y - 1;
      z := z + 1;
    }
    assert z == n;
    result := 0;
    return;
  }
}
