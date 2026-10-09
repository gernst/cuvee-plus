// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_strcpy_original-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_strcpy_original-2.yml (expected: safe), translated from the C program by hand:
// src is copied into dst up to the first 0, and the copied prefix is checked to agree by a loop with the same
// test
//
// findings: open: the second loop with the same test as the copy needs that it does not run beyond the exit n₂₃ of
// the first, which is the iteration constraint of the second loop, src != 0 at all its iterations, instantiated at
// n₂₃, against the exit src[n₂₃] == 0 of the first (see standard_vararg_ground); no lemmas tried

method main() {
  var i: int;
  var j: int;
  var v: int;
  var src: array<int, int>;
  var dst: array<int, int>;
  i := 0;
  j := 0;
  while j < 100000 {
    havoc v;
    src := src[j := v];
    j := j + 1;
  }
  while i < 100000 && src[i] != 0 {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  i := 0;
  while i < 100000 && src[i] != 0 {
    assert dst[i] == src[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall dst₅: array<int, int>, V?₁₀: seq<int>, n₂₃: int, K₂₅: Trace<int>,
//          I₂₇: Trace<int>, n₃₁: int, K₃₃: Trace<int>, I₃₄: Trace<int> ::
//     K₂₅ == counter(0, 1, n₂₃)
//       && I₂₇ == counter(0, 1, n₂₃)
//       && n₂₃ < 100001
//       && invs(for ⌊K₂₅⌋, ⌊I₂₇⌋ check k₂₄, i₂₂ :: earlier(k₂₄, V?₁₀) != 0)
//       && 0 <= n₂₃
//       && K₃₃ == counter(0, 1, n₃₁)
//       && I₃₄ == counter(0, 1, n₃₁)
//       && invs(for ⌊K₃₃⌋, ⌊I₃₄⌋ check k₃₂, i₃₀ :: earlier(k₃₂, V?₁₀) != 0)
//       && invs(for ⌊K₃₃⌋, ⌊I₃₄⌋
//               check k₃₂, i₃₀ ::
//                 (if k₃₂ < n₂₃ then earlier(k₃₂, V?₁₀) else dst₅[k₃₂])
//                   == earlier(k₃₂, V?₁₀))
//       && 0 <= n₃₁ < 100000
//       && earlier(n₃₁, V?₁₀) != 0
//       ==> n₂₃ < 100000 && earlier(n₂₃, V?₁₀) != 0
//         || (if n₃₁ < n₂₃ then earlier(n₃₁, V?₁₀) else dst₅[n₃₁])
//           == earlier(n₃₁, V?₁₀)
