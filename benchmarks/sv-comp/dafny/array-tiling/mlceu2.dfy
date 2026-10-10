// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-tiling/mlceu2.dfy
// SV-COMP array-tiling/mlceu2.yml (expected: safe), translated from the C program by hand:
// a[i] = 1 if i >> 16 > 250, else 0, which is 0 for the sizes below 100000, which is checked; i >> 16 is i /
// 65536 for i >= 0
//
// findings: the store depends on a case split on the position, joined into a store of a conditional value by a
// lemma generic in the condition and the values, after which teq.dfy reads it; the condition 250 < k / 65536 is
// false for positions below the size 100000 by a lemma that bounds integer division, whose left-hand side is a
// comparison of a quotient (not about traces), since the simplifier knows no bounds of division; closed (no output)

// a store at the iteration k whose value depends on a case split on k is a store of the conditional value (with a
// further dependency ys)
lemma {:rw} {:teq} trace_1(a0: array<int, int>, n: Nat, ys: List<int>, C: (int) -> bool, F: (int) -> int,
                           G: (int) -> int)
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: case C(k) => a[k := F(k)] case !C(k) => a[k := G(k)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[k := if C(k) then F(k) else G(k)])

// a bound of integer division by a positive d (not about traces): a nonnegative x below d * (b + 1) has a quotient of
// at most b; the left-hand side is a comparison, whose side conditions are closed once x, d, b are instantiated
lemma {:rw} {:teq} lemma_1(x: int, d: int, b: int)
  requires 0 < d && 0 <= x && x < d * (b + 1)
  ensures (b < x / d) <==> false

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  S := *;
  if S > 1 && S < 100000 {
    i := 0;
    while i < S {
      if i / 65536 > 250 {
        a := a[i := 1];
      } else {
        a := a[i := 0];
      }
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] == 0;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
