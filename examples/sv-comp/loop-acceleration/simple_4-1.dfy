// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/simple_4-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/simple_4-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of simple_1-1 with other constants or assertions; checks !(x % 2)

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  {
    var x: int;
    x := 268435441;
    while x > 1 {
      x := x - 2;
    }
    assert !(((remainder(x, 2))) != 0);
  }
}
