// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-fpi/pcomp.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/pcomp.yml (expected: safe), translated from the C program by hand: three
// arrays by recurrences: a the multiples of 6 from 6, b its partial sums plus 1, c the partial sums of b, which are
// the cubes i * i * i
//
// findings: three recurrences, whose closed forms are sums of the added terms (see eqn1, sqm), the third one a sum
// of 3 * k + 3 * k * k, which teq.dfy splits by linearity; a lemma states the sum of 3 * k * k as the rest of the
// telescoping sum of (k + 1)^3 - k^3 - 1, such that the division atoms cancel, and a lemma halves the even
// polynomial; -split splits the exits; closed (no output). Attempt: Faulhaber's formula leaves divisions by 2 and
// 6, which are not combined
// note: 3 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function sum(values: seq<int>): int

// the differences (k + 1)^3 - k^3 - 1 = 3 * k + 3 * k * k telescope to n^3 - n over 0, ..., n - 1; teq.dfy splits such
// a sum by linearity first, with the sum of the counter (n * n - n) / 2, hence the lemma states the sum of 3 * k * k
// as the rest, in the normal form of the simplifier, such that the division atoms cancel; Faulhaber's formula for the
// squares would leave divisions by 2 and 6, which are not combined
lemma {:rw} {:free} {:teq} forall n: int ::
  sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: 3 * k * k)) == n * n * n - n - 3 * ((-n + n * n) / 2)

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  N := *;
  assume 0 < N <= 536870911;
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
    assert c[i] == i * i * i;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
