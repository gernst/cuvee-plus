// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/eqn1.dfy
// SV-COMP array-fpi/eqn1.yml (expected: safe), translated from the C program by hand: a holds
// the even numbers 2, 4, ..., by a recurrence, and b the partial sums of a plus 1, which are i * i + i + 1
//
// findings: both arrays are filled by recurrences, a[i] = a[i - 1] + 2 and b[i] = b[i - 1] + a[i - 1], whose closed
// form is the initial element plus the sum of the added terms over the positions before, by one lemma generic in
// the added term G, which teq.dfy sums as linear terms over counters; the remaining arithmetic, the division by 2
// of a polynomial with even coefficients, is a lemma in the normal form of the simplifier; closed (no output)
// note: 2 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  N := *;
  assume 0 < N <= 536870911;
  a := a[0 := 2];
  b := b[0 := 1];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 2];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == i * i + i + 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
