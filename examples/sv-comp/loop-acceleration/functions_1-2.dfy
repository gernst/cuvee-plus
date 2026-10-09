// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/functions_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/functions_1-2.yml (expected: unsafe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of functions_1-1 with other constants or assertions; checks x % 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method f(z: int) returns (result: int) {
  result := z + 2;
  return;
}

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int;
    x := 0;
    while x < N {
      x := f(x);
    }
    assert (((remainder(x, 2))) != 0);
  }
}
