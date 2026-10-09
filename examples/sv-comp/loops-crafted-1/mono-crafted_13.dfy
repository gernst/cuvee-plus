// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_13.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_13.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks (x%2==0)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int;
    var y: int;
    var z: int;
    x := 0;
    y := 50000;
    z := 0;
    x := 0;
    while x < N {
      if x < 50000 {
        x := x + 1;
      } else {
        x := x + 2;
        y := y + 2;
      }
    }
    while y > z {
      y := y - 1;
      x := x - 1;
    }
    assert (remainder(x, 2)) == 0;
    result := 0;
    return;
  }
}
