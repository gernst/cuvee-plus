// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/hh2012-ex1b.dfy
// SV-COMP ReachSafety-Loops/loop-lit/hh2012-ex1b.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks j <= 100; j == 100; i <= 100; i == 100
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var i: int;
    i := 0;
    while i < N {
      var j: int;
      j := 0;
      while j < N {
        j := j + 1;
        assert j <= N;
      }
      assert j == N;
      i := i + 1;
      assert i <= N;
    }
    assert i == N;
    result := 0;
    return;
  }
}
