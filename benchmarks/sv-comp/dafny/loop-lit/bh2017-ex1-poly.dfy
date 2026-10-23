// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/bh2017-ex1-poly.dfy
// SV-COMP loop-lit/bh2017-ex1-poly.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 0 <= j; j <= 2 * i; 2 * i <= j + 6; j <= 4; 0 <= j; j <= 2
// * i; 2 * i <= j + 6; j <= 4

method main() returns (result: int) {
  var i: int;
  var j: int;
  i := 0;
  while i < 4 {
    j := 0;
    while j < 3 {
      i := i + 1;
      j := j + 2;
      assert 0 <= j;
      assert j <= 2 * i;
      assert 2 * i <= j + 6;
      assert j <= 4;
    }
    assert 0 <= j;
    assert j <= 2 * i;
    assert 2 * i <= j + 6;
    assert j <= 4;
    i := i - (quot(j, 2)) + 1;
  }
  result := 0;
  return;
}
