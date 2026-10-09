// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/sumt2.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/sumt2.yml (expected: safe), translated from the C program by hand: l
// counts to n, at most SIZE == 20000001, unsigned, and i and j count the even and the odd values of l, which add up
// to l
//
// findings: i and j count the even and odd iterations, which teq.dfy introduces as counts of a map of k % 2 and of
// k % 2 == 0; lemmas count false as the others than true, the iterations where k % 2 == r as the occurrences of r,
// and the remainders (see half.dfy), which gives both counts the same closed form, since they differ in the names
// of their bound variables otherwise (see TODO.md), and the length of the iterations of a counter; the lemmas keep
// the dependencies as matched; closed (no output)
// note: 2 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function count<a>(e: a, vs: seq<a>): int

// the length of the iterations of a counter
lemma {:rw} {:free} {:teq} forall i: int, c: int, n: int ::
  |⌊counter(i, c, n)⌋| == n

// the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m (see half.dfy), which gives both
// counts the same closed form, since they differ in the names of their bound variables
lemma {:rw} {:free} {:teq} forall n: int, m: int, r: int, hs: seq<int> ::
  if 0 < m && 0 <= r < m
  then count(r, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: k % m)) == (n + m - 1 - r) / m

method main() {
  var n: int;
  var i: int;
  var j: int;
  var l: int;
  n := *;
  assume 0 <= n <= 20000001;
  i := 0;
  j := 0;
  l := 0;
  while l < n {
    if l % 2 == 0 {
      i := i + 1;
    } else {
      j := j + 1;
    }
    l := l + 1;
  }
  assert i + j == l;
}

// remaining goals of -teq -simplify:
// none
