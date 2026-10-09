// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/simple_4-2_abstracted.dfy
// SV-COMP loop-acceleration/simple_4-2_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_1-1_abstracted with other constants or assertions; checks
// !(x % 2)

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  {
    var x: int;
    x := 268435440;
    if x > 0 {
      x := *;
    assume 0 <= x;
    }
    if x > 0 {
      assume false;
    }
    assert !(((remainder(x, 2))) != 0);
  }
}
