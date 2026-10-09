// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/rewnif.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/rewnif.yml (expected: safe), translated from the C program by hand:
// a[i + 1] = i (if in bounds) and then a[i] = i, and a[i] >= i is checked
//
// findings: as rew with the stored values k at k + 1 and k at k, by the same lemma; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a loop over k = 0, ..., n - 1 that stores F(k) at the next position k + 1 while it is below m, and then G(k) at k,
// overwrites each position j below n by G(j) last, and leaves F(n - 1) at n if that is below m (with a further
// dependency ys)
lemma {:rw} {:teq} current_1(a0: array<int, int>, n: int, m: int, j: int, ys: seq<int>, F: (int) -> int,
                             G: (int) -> int)
  ensures if 0 <= n
    then current(trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y ::
                         case k + 1 < m => a[k + 1 := F(k)][k := G(k)] case m == k + 1 => a[k := G(k)]))[j]
      == if 0 <= j < n then G(j) else if j == n && 0 < n < m then F(n - 1) else a0[j]

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  S := *;
  if S > 1 && S < 100000 {
    i := 0;
    while i < S {
      if i + 1 < S {
        a := a[i + 1 := i];
      }
      a := a[i := i];
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] >= i;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
