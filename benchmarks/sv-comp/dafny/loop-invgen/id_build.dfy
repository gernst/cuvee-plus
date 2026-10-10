// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invgen/id_build.dfy
// SV-COMP loop-invgen/id_build.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks 0 <= nlen-1-i; nlen-1-i < nlen

method main() returns (result: int) {
  var tmp₁: int;
  var offset: int;
  var length: int;
  var nlen: int;
  var i: int;
  var j: int;
  tmp₁ := *;
  nlen := tmp₁;
  i := 0;
  while i < nlen {
    j := 0;
    while j < 8 {
      assert 0 <= nlen - 1 - i;
      assert nlen - 1 - i < nlen;
      j := j + 1;
    }
    i := i + 1;
  }
  result := 0;
  return;
}
