// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/gj2007.dfy
// SV-COMP loop-lit/gj2007.yml (expected: safe), translated from the C program by hand: x counts
// to 100, and y, initially 50, counts along in the second half, from x == 50 on, hence y is 100 at the end
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): y counts in the second half
// only, whose guard x < 50 refers to the counter x
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 100, at least 50

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 50 <= N;
  x := 0;
  y := 50;
  while x < N {
    if x < 50 {
      x := x + 1;
    } else {
      x := x + 1;
      y := y + 1;
    }
  }
  assert y == N;
}

// remaining goals of -teq -simplify:
// none
