// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loops-crafted-1/mono-crafted_11.dfy
// SV-COMP loops-crafted-1/mono-crafted_11.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks (x%2)==0
// note: the concrete loop bounds are symbolic: N = 20 * K for 100000000, and the threshold that is a fraction of
// it, 2 * K = N / 10 for 10000000; a multiple of 20, such that the threshold is even and x, which counts by 2 from
// there, ends at an even value, as for the original bound

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  var K: int;
  var x: int;
  assume 0 < K;
  assume N == 20 * K;
  x := 0;
  while x < N {
    if x < 2 * K {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert (remainder(x, 2)) == 0;
  result := 0;
  return;
}
