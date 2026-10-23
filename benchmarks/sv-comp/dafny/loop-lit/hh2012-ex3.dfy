// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/hh2012-ex3.dfy
// SV-COMP loop-lit/hh2012-ex3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks 0 <= j; j <= i; i <= j + 3; j <= 4; 0 <= j; j <= i; i <= j + 3; j <=
// 4

method main() returns (result: int) {
  var i: int;
  var j: int;
  i := 0;
  while i < 4 {
    j := 0;
    while j < 4 {
      i := i + 1;
      j := j + 1;
      assert 0 <= j;
      assert j <= i;
      assert i <= j + 3;
      assert j <= 4;
    }
    assert 0 <= j;
    assert j <= i;
    assert i <= j + 3;
    assert j <= 4;
    i := i - j + 1;
  }
  result := 0;
  return;
}
