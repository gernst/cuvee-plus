// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-tiling/rew.dfy
// SV-COMP array-tiling/rew.yml (expected: safe), translated from the C program by hand:
// a[i + 1] = 0 (if in bounds) and then a[i] = 3, such that each element is overwritten by 3, which is checked
// to be at least 2
//
// findings: each iteration k stores at k + 1 (while below the size) and then at k, so each position below n is
// overwritten last by the second store, by a lemma generic in both stored values, whose guards are the two cases of
// -teq; closed (no output) (rewnifrev and rewnifrev2 are variants, backwards)

// a loop over k = 0, ..., n - 1 that stores F(k) at the next position k + 1 while it is below m, and then G(k) at k,
// overwrites each position j below n by G(j) last, and leaves F(n - 1) at n if that is below m (with a further
// dependency ys)
lemma {:rw} {:teq} current_1(a0: array<int, int>, n: Nat, m: int, j: int, ys: List<int>, F: (int) -> int,
                             G: (int) -> int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y ::
                         case k + 1 < m => a[k + 1 := F(k)][k := G(k)] case m == k + 1 => a[k := G(k)]))[j]
    == if 0 <= j < integer(n) then G(j) else if j == integer(n) && 0 < integer(n) < m then F(integer(n) - 1) else a0[j]

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  S := *;
  if S > 1 {
    i := 0;
    while i < S {
      if i + 1 < S {
        a := a[i + 1 := 0];
      }
      a := a[i := 3];
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] >= 2;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
