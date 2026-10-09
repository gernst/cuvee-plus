// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_vardep_1.dfy
// SV-COMP loop-crafted/simple_vardep_1.yml (expected: safe), translated from the C program by
// hand: i, j, k grow by 1, 2, 3 while k < 0x0fffffff, and k == i + j is checked in the loop (unsigned int is int,
// there is no wrap-around below the bound)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the three counters
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() {
  var N: int;
  var i: int;
  var j: int;
  var k: int;
  assume 0 < N;
  i := 0;
  j := 0;
  k := 0;
  while k < N {
    i := i + 1;
    j := j + 2;
    k := k + 3;
    assert k == i + j;
  }
}

// remaining goals of -teq -simplify:
// none
