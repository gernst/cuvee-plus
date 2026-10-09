// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/hh2012-ex2b.dfy
// SV-COMP loop-lit/hh2012-ex2b.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of hh2012-ex1b with other constants or assertions; checks n <= 60; n == 60

method main() returns (result: int) {
  var tmp₁: bool;
  var n: int;
  n := 0;
  while (1 != 0) {
    assert n <= 60;
    tmp₁ := *;
    if tmp₁ {
      if n < 60 {
        n := n + 1;
      } else {
        assert n == 60;
        n := 0;
      }
    }
  }
  result := 0;
  return;
}
