// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/in-de20.dfy
// SV-COMP loops-crafted-1/in-de20.yml (expected: safe), translated from the C program by hand: x
// counts down from n, unsigned, to 0 while y counts up, then x counts up again while z counts y down, and x is n
// then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var n: int;
  var x: int;
  var y: int;
  var z: int;
  n := *;
  assume 0 <= n;
  x := n;
  y := 0;
  while x > 0 {
    x := x - 1;
    y := y + 1;
  }
  z := y;
  while z > 0 {
    x := x + 1;
    z := z - 1;
  }
  assert x == n;
}

// remaining goals of -teq -simplify:
// none
