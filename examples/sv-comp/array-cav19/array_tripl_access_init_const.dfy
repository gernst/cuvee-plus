// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_tripl_access_init_const.dfy
// SV-COMP array-cav19/array_tripl_access_init_const.yml (expected: safe), translated from the C program by hand:
// the positions 3 i, 3 i + 1, and 3 i + 2 are set to 0 for i = 0, ..., N, and all positions up to 3 N are
// checked to be nonnegative
//
// findings: as array_doub_access_init_const, with stores at 3 k, 3 k + 1, 3 k + 2 and a closed form modulo 3; open
// for the same reason, n₁₄ < 3 * n₆
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// a loop that stores c, d, e at the positions 3 k, 3 k + 1, 3 k + 2 in the iterations k = 0, ..., n - 1 fills the
// positions below 3 n, by their remainder modulo 3, and keeps the others (with a further dependency ys that the
// update does not use)
lemma {:rw} {:teq} current_1(a0: array<int, int>, n: Nat, j: int, c: int, d: int, e: int, ys: List<int>)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[3 * k := c][3 * k + 1 := d][3 * k + 2 := e]))[j]
    == if 0 <= j < 3 * integer(n) then (if j % 3 == 0 then c else if j % 3 == 1 then d else e) else a0[j]

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i <= N {
    a := a[3 * i := 0];
    a := a[3 * i + 1 := 0];
    a := a[3 * i + 2 := 0];
    i := i + 1;
  }
  i := 0;
  while i <= 3 * N {
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
//                 0 <= (if k₁₅ < 3 * n₆ then 0 else a₃[k₁₅]))
//       && 0 <= n₁₄ <= 300000
//       ==> 0 <= (if n₁₄ < 3 * n₆ then 0 else a₃[n₁₄])
