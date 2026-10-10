// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_12.dfy
// SV-COMP loops-crafted-1/mono-crafted_12.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks !(z%2)
// note: the concrete loop bounds are symbolic, arbitrary positive values: y for 10000000

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var x: int;
  var y: int;
  var z: int;
  x := 0;
  y := *;
  assume 0 < y;
  z := 0;
  while x < y {
    if x >= 5000000 {
      z := z + 2;
    }
    x := x + 1;
  }
  assert !(((remainder(z, 2))) != 0);
  result := 0;
  return;
}
