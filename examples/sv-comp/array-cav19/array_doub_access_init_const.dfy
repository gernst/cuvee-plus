// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_doub_access_init_const.dfy
// SV-COMP ReachSafety-Arrays/array-cav19/array_doub_access_init_const.yml (expected: safe), translated from the C
// program by hand: the positions 2 i and 2 i + 1 are set to 0 for i = 0, ..., N, and all positions up to 2 N are
// checked to be nonnegative
//
// findings: the read of a loop that stores at 2 k and 2 k + 1 has a closed form by the remainder modulo 2, by one
// lemma generic in the stored values; open: the goal needs n₁₄ < 2 * n₆ from n₁₄ <= 200000 and 100000 < n₆, which
// the difference constraints of the simplifier do not give, since they have no coefficients, and the interval
// 100000 < n₆ < 100002 is not narrowed to n₆ == 100001 (see TODO.md)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a loop that stores c at the even position 2 k and d at the odd position 2 k + 1 in the iterations k = 0, ..., n - 1
// fills the positions below 2 n, alternating between c and d, and keeps the others (with a further dependency ys
// that the update does not use, e.g. a second counter)
lemma {:rw} {:teq} current_1(a0: array<int, int>, n: int, j: int, c: int, d: int, ys: seq<int>)
  ensures if 0 <= n
    then current(trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[2 * k := c][2 * k + 1 := d]))[j]
      == if 0 <= j < 2 * n then (if j % 2 == 0 then c else d) else a0[j]

method main() {
  var i: int;
  var N: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N;
  i := 0;
  while i <= N {
    a := a[2 * i := 0];
    a := a[2 * i + 1 := 0];
    i := i + 1;
  }
  i := 0;
  while i <= 2 * N {
    assert a[i] >= 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, n₆: int, n₁₄: int, K₁₆: Trace<int>,
//          I₁₇: Trace<int> ::
//     n₆ < 100002
//       && 100000 < n₆
//       && K₁₆ == counter(0, 1, n₁₄)
//       && I₁₇ == counter(0, 1, n₁₄)
//       && invs(for ⌊K₁₆⌋, ⌊I₁₇⌋
//               check k₁₅, i₁₃ ::
//                 0 <= (if k₁₅ < 2 * n₆ then 0 else a₃[k₁₅]))
//       && 0 <= n₁₄ <= 200000
//       ==> 0 <= (if n₁₄ < 2 * n₆ then 0 else a₃[n₁₄])
