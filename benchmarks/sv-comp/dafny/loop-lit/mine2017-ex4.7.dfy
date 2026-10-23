// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.7.dfy
// SV-COMP loop-lit/mine2017-ex4.7.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mine2017-ex4.10 with other constants or assertions; checks 0 <= x; x <= 40

method main() returns (result: int) {
  var tmp₁: bool;
  var tmp₂: bool;
  var x: int;
  x := 0;
  while true {
    tmp₁ := *;
    if (if tmp₁ then 1 else 0) != 0 {
      break;
    }
    assert 0 <= x;
    assert x <= 40;
    tmp₂ := *;
    if (if tmp₂ then 1 else 0) == 0 {
      x := x + 1;
      if x > 40 {
        x := 0;
      }
    }
  }
  result := 0;
  return;
}
