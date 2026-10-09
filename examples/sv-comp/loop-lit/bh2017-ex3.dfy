// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/bh2017-ex3.dfy
// SV-COMP loop-lit/bh2017-ex3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks m <= 60; n <= 60; m == 60; n == 60

method main() returns (result: int) {
  var tmp₁: bool;
  var tmp₂: bool;
  var tmp₃: bool;
  var m: int;
  var n: int;
  m := 0;
  n := 0;
  while (1 != 0) {
    assert m <= 60;
    assert n <= 60;
    tmp₁ := *;
    if tmp₁ {
      tmp₂ := *;
      if tmp₂ {
        if m < 60 {
          m := m + 1;
        } else {
          assert m == 60;
          m := 0;
        }
      }
    } else {
      tmp₃ := *;
      if tmp₃ {
        if n < 60 {
          n := n + 1;
        } else {
          assert n == 60;
          n := 0;
        }
      }
    }
  }
  result := 0;
  return;
}
