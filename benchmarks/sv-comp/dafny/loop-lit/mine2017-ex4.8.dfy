// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.8.dfy
// SV-COMP loop-lit/mine2017-ex4.8.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mine2017-ex4.10 with other constants or assertions; checks 0 <= v; v <= 1

method main() returns (result: int) {
  var tmp₁: bool;
  var v: int;
  v := 0;
  while true {
    tmp₁ := *;
    if (if tmp₁ then 1 else 0) != 0 {
      break;
    }
    assert 0 <= v;
    assert v <= 1;
    if v == 0 {
      v := 1;
    }
  }
  result := 0;
  return;
}
