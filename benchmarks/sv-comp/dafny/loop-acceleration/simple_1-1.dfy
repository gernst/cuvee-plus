// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_1-1.dfy
// SV-COMP loop-acceleration/simple_1-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of simple_1-2 with other constants or assertions; checks x % 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  var x: int;
  assume 0 < N;
  x := 0;
  while x < N {
    x := x + 2;
  }
  assert (((remainder(x, 2))) != 0);
}
