// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-cav19/array_init_nondet_vars.dfy
// SV-COMP array-cav19/array_init_nondet_vars.yml (expected: safe), translated from the C program
// by hand: a[i] = i + j + k with positive j and a positive k chosen in each iteration, and a[i] >= i + 2 is checked
//
// findings: the values k chosen in each iteration are positive, an iteration constraint, which is abstracted by the
// predicate above and then instantiated at the read position by a lemma whose left-hand side is a comparison b <=
// earlier(j, xs) + d; closed (no output)

// the first n values of xs are above c, an auxiliary predicate, which is not defined
predicate {:teq} above(c: int, n: Nat, xs: List<int>)

// the iteration constraint of values xs that are chosen above c in each of n iterations (with a further dependency
// hs that the constraint does not use), abstracted by the predicate above
lemma {:rw} {:teq} invs_1(c: int, n: Nat, hs: List<int>, xs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: c < x) <==> above(c, n, xs)

// a value chosen at an iteration j before n, i.e., above c, plus d, is at least b if b <= c + 1 + d; the left-hand
// side is a comparison, whose side conditions are an atom and closed comparisons
lemma {:rw} {:teq} earlier_1(c: int, n: Nat, xs: List<int>, j: Nat, b: int, d: int)
  requires above(c, n, xs) && integer(j) < integer(n) && b <= c + 1 + d
  ensures b <= earlier(j, xs) + d

method main() {
  var i: int;
  var j: int;
  var n: int;
  var k: int;
  var a: array<int, int>;
  j := *;
  n := *;
  assume j > 0;
  i := 1;
  while i < n {
    k := *;
    assume k > 0;
    a := a[i := i + j + k];
    i := i + 1;
  }
  i := 1;
  while i < n {
    assert a[i] >= i + 2;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
