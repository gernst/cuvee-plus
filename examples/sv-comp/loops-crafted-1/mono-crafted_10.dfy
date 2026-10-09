// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_10.dfy
// SV-COMP loops-crafted-1/mono-crafted_10.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: z counts up from 5000000 in the second half of x up to 10000000, and z == x is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (mono-crafted_9, _11 to _14 are
// variants)
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: M for 5000000, y at least M
// for 10000000

method main() returns (result: int) {
  var M: int, x: int, y: int, z: int;
  x := 0;
  assume 0 < M;
  y := *;
  assume M <= y;
  z := M;
  while x < y {
    if x >= M {
      z := z + 1;
    }
    x := x + 1;
  }
  assert z == x;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
