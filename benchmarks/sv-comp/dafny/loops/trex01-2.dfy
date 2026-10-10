// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/trex01-2.dfy
// SV-COMP loops/trex01-2.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of trex01-1 with other constants or assertions

method f(d: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: bool;
  var tmp₅: bool;
  var x: int;
  var y: int;
  var k: int;
  var z: int;
  var c: bool;
  tmp₁ := *;
  x := tmp₁;
  tmp₂ := *;
  y := tmp₂;
  tmp₃ := *;
  k := tmp₃;
  z := 1;
  while z < k {
    z := 2 * z;
  }
  assert z >= 1;
  if !(x >= -1000000) {
    return;
  }
  if !(y >= -1000000) {
    return;
  }
  if !(k >= -1000000) {
    return;
  }
  while x > 0 && y > 0 {
    tmp₄ := *;
    c := tmp₄;
    if c {
      x := x - d;
      tmp₅ := *;
      y := (if tmp₅ then 1 else 0);
      z := z - 1;
    } else {
      y := y - d;
    }
  }
}

method main() returns (result: int) {
  var tmp₆: bool;
  var c: bool;
  tmp₆ := *;
  c := tmp₆;
  if c {
    f(1);
  } else {
    f(2);
  }
  result := 0;
  return;
}
