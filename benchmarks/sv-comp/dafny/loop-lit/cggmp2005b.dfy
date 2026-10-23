// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/cggmp2005b.dfy
// SV-COMP loop-lit/cggmp2005b.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks k == 4
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100, M for 20

method main() returns (result: int) {
  var N: int;
  var M: int;
  var i: int;
  var j: int;
  var k: int;
  assume 0 < N;
  assume 0 < M;
  i := 0;
  k := 9;
  j := -N;
  while i <= N {
    i := i + 1;
    while j < M {
      j := i + j;
    }
    k := 4;
    while k <= 3 {
      k := k + 1;
    }
  }
  assert k == 4;
  result := 0;
  return;
}
