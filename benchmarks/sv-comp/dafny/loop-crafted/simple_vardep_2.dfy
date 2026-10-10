// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-crafted/simple_vardep_2.dfy
// SV-COMP loop-crafted/simple_vardep_2.yml (expected: safe), translated from the C program by
// hand: as simple_vardep_1, with k == 3 i and j == 2 i checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
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
    assert k == 3 * i && j == 2 * i;
  }
}

// remaining goals of -teq -simplify:
// none
