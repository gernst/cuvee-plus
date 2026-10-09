// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/motivex.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/motivex.yml (expected: safe), translated from the C program by hand:
// the fields p and q of a struct are set to i, and then to k and k * k for some i; p == q or q == p * p is
// checked; unsigned short is int without wrap-around (the C program writes beyond the 10000 elements)
//
// findings: the second loop stores k and k * k only in some iterations, which the lemma for guarded stores that
// otherwise keep the array reads at a position, generic in the condition and the stored value; open: the remaining
// disjunction needs a case split on the shared test of the conditionals, which a lemma on equations of conditionals
// with the same test does for the first disjunct, while a lemma on the product of two such conditionals does not
// match the product (see TODO.md)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// a store at the iteration k that is made only if C holds of the values of the iteration, read at j: the value of
// the iteration j if it is one of the first n and C holds there, otherwise the initial value (with further
// dependencies hs, cs, vs)
lemma {:rw} {:teq} current_1<b>(a0: array<int, b>, n: int, j: int, hs: seq<int>, cs: seq<int>, vs: seq<int>,
                                C: (int, int, int) -> bool, V: (int, int, int) -> b)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs, cs, vs do a, k, h, c, v ::
                  case C(h, c, v) => a[k := V(h, c, v)] case !C(h, c, v) => a))[j]
    == if 0 <= j < n && C(earlier(j, hs), earlier(j, cs), earlier(j, vs))
       then V(earlier(j, hs), earlier(j, cs), earlier(j, vs))
       else a0[j]

// conditionals with the same test in an equation are a single case split (not about traces)
lemma {:rw} {:teq} lemma_1<b>(c: bool, x: b, y: b, u: b, v: b)
  ensures (if c then x else y) == (if c then u else v) <==> if c then x == u else y == v

method main() {
  var N: int;
  var i: int;
  var b: int;
  var k: int;
  var p: array<int, int>;
  var q: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    p := p[i := i];
    q := q[i := i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := *;
    if b != 0 {
      k := *;
      p := p[i := k];
      q := q[i := k * k];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert p[i] == q[i] || q[i] == p[i] * p[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall B?₂₅: seq<int>, K?₂₆: seq<int>, n₄₃: int, K₄₅: Trace<int>,
//          I₄₆: Trace<int> ::
//     K₄₅ == counter(0, 1, n₄₃)
//       && I₄₆ == counter(0, 1, n₄₃)
//       && invs(for ⌊K₄₅⌋, ⌊I₄₆⌋
//               check k₄₄, i₄₂ ::
//                 (if earlier(k₄₄, B?₂₅) != 0
//                  then earlier(k₄₄, K?₂₆)
//                    == earlier(k₄₄, K?₂₆) * earlier(k₄₄, K?₂₆)
//                  else true)
//                   || (if earlier(k₄₄, B?₂₅) != 0
//                       then earlier(k₄₄, K?₂₆) * earlier(k₄₄, K?₂₆)
//                       else k₄₄)
//                     == (if earlier(k₄₄, B?₂₅) != 0
//                         then earlier(k₄₄, K?₂₆)
//                         else k₄₄)
//                       * (if earlier(k₄₄, B?₂₅) != 0
//                          then earlier(k₄₄, K?₂₆)
//                          else k₄₄))
//       && 0 <= n₄₃ < 1000000
//       ==> (if earlier(n₄₃, B?₂₅) != 0
//            then earlier(n₄₃, K?₂₆) == earlier(n₄₃, K?₂₆) * earlier(n₄₃, K?₂₆)
//            else true)
//         || (if earlier(n₄₃, B?₂₅) != 0
//             then earlier(n₄₃, K?₂₆) * earlier(n₄₃, K?₂₆)
//             else n₄₃)
//           == (if earlier(n₄₃, B?₂₅) != 0 then earlier(n₄₃, K?₂₆) else n₄₃)
//             * (if earlier(n₄₃, B?₂₅) != 0 then earlier(n₄₃, K?₂₆) else n₄₃)
