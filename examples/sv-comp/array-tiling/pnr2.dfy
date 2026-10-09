// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/pnr2.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/pnr2.yml (expected: safe), translated from the C program by hand:
// values read from a port are stored at 2 i - 2 and 2 i - 1, replaced by 10 if they are 0, and each element is
// checked to be nonzero
//
// findings: open: the stores at 2 k and 2 k + 1 of values read from a port, replaced by 10 if 0, are split by -teq
// into four cases over three sequences of fresh values, whose read at a position needs the closed form modulo 2 of
// a guarded update with four cases; no lemmas tried (pnr3 to pnr5 are variants)

method main() {
  var S: int;
  var i: int;
  var value: int;
  var a: array<int, int>;
  havoc S;
  if S > 1 && S < 100000 {
    if S % 2 != 0 {
      return;
    }
    i := 1;
    while i <= S / 2 {
      havoc value;
      if value != 0 {
        a := a[i * 2 - 2 := value];
      } else {
        a := a[i * 2 - 2 := 10];
      }
      havoc value;
      if value != 0 {
        a := a[i * 2 - 1 := value];
      } else {
        a := a[i * 2 - 1 := 10];
      }
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] != 0;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₄: array<int, int>, S₅: int, a₂₂: array<int, int>, n₁₅: int,
//          K₁₇: Trace<int>, A₁₉: Trace<array<int, int>>, I₂₀: Trace<int>,
//          Value?₁₂: seq<int>, Value?₁₃: seq<int>, Value?₁₄: seq<int>, n₂₈: int,
//          K₃₀: Trace<int>, I₃₁: Trace<int> ::
//     !(1 < S₅ < 100000
//         && S₅ % 2 == 0
//         && K₁₇ == counter(0, 1, n₁₅)
//         && a₂₂ == current(A₁₉)
//         && A₁₉
//           == trace(a₄, for ⌊K₁₇⌋, ⌊I₂₀⌋, Value?₁₂, Value?₁₃, Value?₁₄
//                        do a₇, k₁₆, i₈, value₉, value₁₀, value₁₁ ::
//                          case value₉ != 0 && value₁₀ != 0 => a₇[
//                            2 * k₁₆ :=
//                            value₉][
//                            2 * k₁₆ + 1 :=
//                            value₁₀]
//                          case value₉ != 0 && value₁₀ == 0 => a₇[
//                            2 * k₁₆ :=
//                            value₉][
//                            2 * k₁₆ + 1 :=
//                            10]
//                          case value₉ == 0 && value₁₁ != 0 => a₇[2 * k₁₆ := 10][
//                            2 * k₁₆ + 1 :=
//                            value₁₁]
//                          case value₉ == 0 && value₁₁ == 0 => a₇[2 * k₁₆ := 10][
//                            2 * k₁₆ + 1 :=
//                            10])
//         && I₂₀ == counter(1, 1, n₁₅)
//         && (n₁₅ == 0 || 0 < S₅ / 2 && n₁₅ == S₅ / 2)
//         && invs(for ⌊K₁₇⌋, ⌊I₂₀⌋, Value?₁₂, Value?₁₃, Value?₁₄
//                 check k₁₆, i₈, value₉, value₁₀, value₁₁ ::
//                   value₉ != 0 && value₁₀ != 0
//                     || value₉ != 0 && value₁₀ == 0
//                     || value₉ == 0 && value₁₁ != 0
//                     || value₉ == 0 && value₁₁ == 0)
//         && 0 <= n₁₅
//         && S₅ / 2 <= n₁₅
//         && K₃₀ == counter(0, 1, n₂₈)
//         && I₃₁ == counter(0, 1, n₂₈)
//         && invs(for ⌊K₃₀⌋, ⌊I₃₁⌋ check k₂₉, i₂₇ :: a₂₂[k₂₉] != 0)
//         && 0 <= n₂₈ < S₅
//         && a₂₂[n₂₈] == 0)
