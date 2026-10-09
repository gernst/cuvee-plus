// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/nested3-1.dfy
// SV-COMP loops-crafted-1/nested3-1.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks z % 4; y % 2; x % 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  var z: int;
  var w: int;
  assume 0 < N;
  x := 0;
  y := 0;
  z := 0;
  w := 0;
  while x < N {
    y := 0;
    while y < N {
      z := 0;
      while z < N {
        z := z + 1;
      }
      assert (((remainder(z, 4))) != 0);
      y := y + 1;
    }
    assert (((remainder(y, 2))) != 0);
    x := x + 1;
  }
  assert (((remainder(x, 2))) != 0);
  result := 0;
  return;
}
