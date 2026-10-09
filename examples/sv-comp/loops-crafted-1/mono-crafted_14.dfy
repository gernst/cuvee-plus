// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_14.dfy
// SV-COMP loops-crafted-1/mono-crafted_14.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks z%2==0; x%2==0
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  var z: int;
  assume 0 < N;
  x := 0;
  y := 500000;
  z := 0;
  x := 0;
  while x < N {
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
  assert (remainder(z, 2)) == 0;
  assert (remainder(x, 2)) == 0;
  result := 0;
  return;
}
