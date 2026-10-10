// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/multivar_1-2.dfy
// SV-COMP loop-acceleration/multivar_1-2.yml (expected: unsafe), translated from the C program by
// hand: the unsafe variant of multivar_1-1, where y starts at x + 1
//
// findings: unsafe, not closed, as expected: x and y are counters from x and x + 1, which differ
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := *;
  assume 0 <= x;
  y := x + 1;
  while x < N {
    x := x + 1;
    y := y + 1;
  }
  assert x == y;
}

// remaining goals of -teq -simplify:
// goal
//   forall x₃: int, y₁₂: int ::
//     !(0 <= x₃
//         && (y₁₂ == x₃ + 1 || x₃ < 1024 && y₁₂ < 1026)
//         && x₃ < y₁₂
//         && 1025 <= y₁₂)
