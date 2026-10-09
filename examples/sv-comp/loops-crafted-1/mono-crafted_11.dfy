// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_11.dfy
// SV-COMP loops-crafted-1/mono-crafted_11.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks (x%2)==0
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000000 and even, since x counts
// by 2 from 10000000 on, which is even, and the assertion is x % 2 == 0, as for the original bound 100000000

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  var x: int;
  assume 0 < N;
  assume N % 2 == 0;
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
