// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/sum04-1.dfy
// SV-COMP loops/sum04-1.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of sum01-2 with other constants or assertions; checks sn==8*(2) || sn == 0

method main() returns (result: int) {
  var i: int;
  var sn: int;
  sn := 0;
  i := 1;
  while i <= 8 {
    if i < 4 {
      sn := sn + 2;
    }
    i := i + 1;
  }
  assert sn == 8 * 2 || sn == 0;
}
