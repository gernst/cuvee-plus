// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/sum01-2.dfy
// SV-COMP loops/sum01-2.yml (expected: safe), translated from the C program by hand: sn adds 2
// for each i from 1 to n, and is 2 * n or 0
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var n: int;
  var sn: int;
  n := *;
  sn := 0;
  assume n < 1000 && n >= -1000;
  i := 1;
  while i <= n {
    sn := sn + 2;
    i := i + 1;
  }
  assert sn == n * 2 || sn == 0;
}

// remaining goals of -teq -simplify:
// none
