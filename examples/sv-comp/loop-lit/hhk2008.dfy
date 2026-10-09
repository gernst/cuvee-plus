// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/hhk2008.dfy
// SV-COMP ReachSafety-Loops/loop-lit/hhk2008.yml (expected: safe), translated from the C program by hand: res
// counts up from a while cnt counts down from b to 0, then res is a + b
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): res and cnt are counters with
// steps 1 and -1

method main() {
  var a: int;
  var b: int;
  var res: int;
  var cnt: int;
  a := *;
  b := *;
  assume a <= 1000000;
  assume 0 <= b <= 1000000;
  res := a;
  cnt := b;
  while cnt > 0 {
    cnt := cnt - 1;
    res := res + 1;
  }
  assert res == a + b;
}

// remaining goals of -teq -simplify:
// none
