// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/eqn2.dfy
// SV-COMP array-fpi/eqn2.yml (expected: safe), translated from the C program by hand: as eqn1
// with steps of 4: a holds 4, 8, ..., b the partial sums of a plus 1, which are checked to be 2 i * i + 2 i + 1
// (eqn3 to eqn5 are variants)
//
// findings: with the recurrence lemma of eqn1 and the halving of (4 * x + 4 * x * x) / 2 in the normal form of the
// simplifier; closed (no output) (eqn3 to eqn5 are variants, which need further halving lemmas)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing; the lemmas
// are those of eqn1, except the arithmetic
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function sum(values: seq<int>): int

// division by 2 of a polynomial with even coefficients, in the normal form of the simplifier (arithmetic, not about
// traces), see eqn1
lemma {:rw} {:teq} lemma_1(x: int)
  ensures (4 * x + 4 * x * x) / 2 == 2 * x + 2 * x * x

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  N := *;
  assume 0 < N <= 536870911;
  a := a[0 := 4];
  b := b[0 := 1];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 4];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert b[i] == 2 * i * i + 2 * i + 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
