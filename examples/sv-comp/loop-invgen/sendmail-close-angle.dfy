// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/sendmail-close-angle.dfy
// SV-COMP loop-invgen/sendmail-close-angle.yml (expected: safe), translated from the C program by
// hand: buf and in count up together nondeterministically until buf reaches bufferlen - 2, below inlen and
// bufferlen, then buf is increased twice, with the bounds checked
//
// findings: open: the loop leaves by the nondeterministic test or the break at buf == bufferlen - 2, and the goal
// needs the iteration constraint k + 2 != bufferlen over the iterations k < n, instantiated at bufferlen - 2, which
// gives n <= bufferlen - 2; a lemma would match a sum with the bound variable k, which patterns do not (see
// TODO.md); no lemmas tried

method main() {
  var inp: int;
  var inlen: int;
  var bufferlen: int;
  var buf: int;
  var buflim: int;
  var b: int;
  inlen := *;
  bufferlen := *;
  if !(bufferlen > 1 && inlen > 0 && bufferlen < inlen) {
    return;
  }
  buf := 0;
  inp := 0;
  buflim := bufferlen - 2;
  b := *;
  while b != 0 {
    if buf == buflim {
      break;
    }
    assert 0 <= buf;
    assert buf < bufferlen;
    buf := buf + 1;
    inp := inp + 1;
    assert 0 <= inp;
    assert inp < inlen;
    b := *;
  }
  assert 0 <= buf;
  assert buf < bufferlen;
  buf := buf + 1;
  assert 0 <= buf;
  assert buf < bufferlen;
  buf := buf + 1;
}

// remaining goals of -teq -simplify:
// goal
//   forall inlen₇: int, bufferlen₈: int, b₉: int, b₂₃: int, n₁₅: int,
//          K₁₇: Trace<int>, Buf₁₈: Trace<int>, Inp₁₉: Trace<int>, B₂₀: Trace<int>,
//          B?₁₄: seq<int> ::
//     1 < bufferlen₈ < inlen₇
//       && K₁₇ == counter(0, 1, n₁₅)
//       && b₂₃ == current(B₂₀)
//       && Buf₁₈ == counter(0, 1, n₁₅)
//       && Inp₁₉ == counter(0, 1, n₁₅)
//       && B₂₀
//         == trace(b₉, for ⌊K₁₇⌋, ⌊Buf₁₈⌋, B?₁₄ do b₁₂, k₁₆, buf₁₀, b₁₃ :: b₁₃)
//       && invs(for ⌊K₁₇⌋, ⌊Buf₁₈⌋, ⌊Inp₁₉⌋, ⌊B₂₀⌋
//               check k₁₆, buf₁₀, inp₁₁, b₁₂ ::
//                 b₁₂ != 0)
//       && invs(for ⌊K₁₇⌋, ⌊Buf₁₈⌋, ⌊Inp₁₉⌋
//               check k₁₆, buf₁₀, inp₁₁ ::
//                 k₁₆ + 2 != bufferlen₈)
//       && n₁₅ <= bufferlen₈
//       && 0 <= n₁₅
//       ==> (b₂₃ != 0 ==> n₁₅ < bufferlen₈) && (b₂₃ == 0 ==> n₁₅ + 1 < bufferlen₈)
