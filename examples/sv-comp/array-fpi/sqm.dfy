// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-fpi/sqm.dfy
// SV-COMP array-fpi/sqm.yml (expected: safe), translated from the C program by hand: b holds the
// odd numbers 1, 3, ..., by a recurrence, and a the squares (i + 1) * (i + 1), from the partial sums of b plus 2
//
// findings: the same recurrences as eqn1; the closed form of b appears in the update of a, guarded by k <= n, which
// -split decides by the case split on the exits of the loops; then the update is a[k] + 2 * k + 3, which the
// recurrence lemma with one added term does not match, since a higher-order summand matches a single summand (see
// TODO.md), but a variant with two added terms does; the remaining arithmetic is the division by 2 of an even
// polynomial, a lemma in the normal form of the simplifier, since a generic (2 * a + 2 * b) / 2 does not match the
// coefficient 4; closed (no output)
// note: 3 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  N := *;
  assume 0 < N <= 536870911;
  b := b[0 := 1];
  a := a[0 := 1];
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + 2];
    i := i + 1;
  }
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + b[i - 1] + 2];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == (i + 1) * (i + 1);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
