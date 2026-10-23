// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/dafny/array-fpi/pcompf.dfy
// SV-COMP array-fpi/pcompf.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of pcomp, which asserts that the cubes are squares
//
// findings: unsafe, not closed with the lemmas of pcomp, as expected
// note: its lemmas are part of teq.dfy now (sum_squares, half_6x_6xx, ...) and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  N := *;
  assume 0 < N;
  a := a[0 := 6];
  b := b[0 := 1];
  c := c[0 := 0];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 6];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 1;
  while i < N {
    c := c[i := c[i - 1] + b[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert c[i] == i * i;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall n₉: int, n₃₅: int, K₃₇: Trace<int>, I₃₈: Trace<int> ::
//     n₉ <= 536870910
//       && 0 < n₉
//       && K₃₇ == counter(0, 1, n₃₅)
//       && I₃₈ == counter(0, 1, n₃₅)
//       && invs(for ⌊K₃₇⌋, ⌊I₃₈⌋ check k₃₆, i₃₄ :: k₃₆ * k₃₆ * k₃₆ == k₃₆ * k₃₆)
//       && 0 <= n₃₅ <= n₉
//       ==> n₃₅ * n₃₅ * n₃₅ == n₃₅ * n₃₅
