// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/sum04-2.dfy
// SV-COMP loops/sum04-2.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: sn grows by 2 in 8 iterations, and sn == 16 or sn == 0 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var i: int, sn: int;
  sn := 0;
  i := 1;
  while i <= 8 {
    sn := sn + 2;
    i := i + 1;
  }
  assert sn == 8 * 2 || sn == 0;
}

// remaining goals of -teq -simplify:
// none
