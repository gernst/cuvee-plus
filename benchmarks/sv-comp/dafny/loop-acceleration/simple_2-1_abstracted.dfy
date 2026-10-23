// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/simple_2-1_abstracted.dfy
// SV-COMP loop-acceleration/simple_2-1_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_1-1_abstracted with other constants or assertions; checks x
// >= 0x0fffffff

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var x: int;
  tmp₁ := *;
  assume 0 <= tmp₁;
  x := tmp₁;
  if x < N {
    x := *;
  assume 0 <= x;
  }
  if x < N {
    assume false;
  }
  assert x >= N;
}
