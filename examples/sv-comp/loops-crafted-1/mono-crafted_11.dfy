// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_11.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_11.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks (x%2)==0
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000000

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int;
    x := 0;
    while x < N {
      if x < 10000000 {
        x := x + 1;
      } else {
        x := x + 2;
      }
    }
    assert (remainder(x, 2)) == 0;
    result := 0;
    return;
  }
}
