// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_6.dfy
// SV-COMP loops-crafted-1/mono-crafted_6.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts to N, by 1 below 3 * N / 4 and by 2 above, and x == N is checked
//
// findings: open: x counts by 1 below 6 * K and by 2 above, up to N = 8 * K, a two-phase counter whose exit is
// reached exactly at N; current_trace_two_phases of teq.dfy needs the guard x < 6 * K, but the simplifier does not
// merge x < 4 * K || x < 6 * K into it, since 4 * K <= 6 * K follows from 0 < K only by comparing coefficients,
// beyond the difference constraints
// note: the concrete loop bounds are symbolic: N = 8 * K for 1000000, and the thresholds and the initial value of y
// that are fractions of it, 4 * K = N / 2 for 500000 and 6 * K = 3 * N / 4 for 750000; a multiple of 8, such that
// x, which counts by 2 from 6 * K, reaches N exactly, as for the original bound

method main() returns (result: int) {
  var N: int;
  var K: int;
  var x: int, y: int, z: int;
  assume 0 < K;
  assume N == 8 * K;
  x := 0;
  y := 4 * K;
  z := 0;
  x := 0;
  while x < N {
    if x < quot(N, 2) {
      x := x + 1;
    } else {
      if x < quot(3 * N, 4) {
        x := x + 1;
      } else {
        x := x + 2;
      }
      y := y + 1;
    }
  }
  assert x == N;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// goal
//   forall K₂: int, x₁₃: int, n₈: Nat, K₁₀: Trace<int>, X₁₁: Trace<int> ::
//     !(0 < K₂
//         && K₁₀ == counter(0, 1, n₈)
//         && x₁₃ == current(X₁₁)
//         && X₁₁
//           == trace(0, for ⌊K₁₀⌋
//                       do x₆, k₉ ::
//                         case x₆ < 4 * K₂ || x₆ < 6 * K₂ => x₆ + 1
//                         case 4 * K₂ <= x₆ && 6 * K₂ <= x₆ => x₆ + 2)
//         && invs(for ⌊K₁₀⌋, ⌊X₁₁⌋ check k₉, x₆ :: x₆ < 8 * K₂)
//         && 0 <= integer(n₈)
//         && 8 * K₂ < x₁₃)
