// ./Cuvee.sh -teq -entry main -prove examples/dafny/algorithms/reverse.dfy
// the reversal of a[0..n) in place, with two pointers i and j that move towards each other
//
// status (Oct 16, 2026): verified with -teq -prove; a wrong postcondition, b[k] == a[n - 2 - k], leaves a goal;
// the two-pointer form makes the positions of the swaps counters, ⌊counter(0, 1, n')⌋ and ⌊counter(n - 1, -1, n')⌋,
// which the lemma on the trace of the swaps matches, whereas the form with one pointer swaps b[i] and b[n - 1 - i],
// arithmetic on the bound variable of the trace, which patterns do not match (TODO.md); the lemmas: the loop test
// i < j is the iteration constraint 2 k + 1 < n, which the lemmas of teq.dfy on bounds of counters do not resolve
// (invs_pairs); the exit leaves the disjunction n' == zero || n' < j + 2 among the facts, which the summary of the
// swaps takes as its side condition, with the final value j of the other pointer bound by it, such that no case
// split is needed (with -split -prove, the second pass relates n' and i by n' == natural(i) only, from which the
// arithmetic does not recover integer(n') == i); the literal -1 in a pattern is not matched, hence the step of the
// counter down is a variable with a side condition

// the loop test i < j of the two pointers, as an iteration constraint over the counter: twice the iterations stay
// below the length, i.e. the pairs are disjoint; the lemmas of teq.dfy resolve bounds on the counter itself only
lemma {:rw} invs_pairs(n: int, m: int, hs: List<int>, gs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, gs check k, h, g :: 2 * k + 1 < m)
    <==> n <= 0 || 2 * n - 1 < m

// the same with the exit of the loop as it stands among the facts, without a case split: the other pointer m, bound
// by the disjunction of the exit, and the end c of the range satisfy n + m == c and m <= n; either the loop did not
// run (n == 0, then c == m <= 0 and the array is unchanged on the range of at most one element) or n < m + 2, which
// gives the bounds of current_reversal
lemma {:rw} current_reversal_exit(a: array<int, int>, c: int, d: int, n: int, j: int, m: int)
  requires n <= 0 || n < m + 2
  requires n + m == c && m <= n && d == -1
  ensures current(trace(a, for ⌊counter(0, 1, n)⌋, ⌊counter(c, d, n)⌋ do b, k, l :: b[k := b[l]][l := b[k]]))[j]
    == if 0 <= j <= c then a[c - j] else a[j]

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> b[k] == a[n - 1 - k]
{
  var i: int;
  var j: int;
  var t: int;
  b := a;
  i := 0;
  j := n - 1;
  while i < j
  {
    t := b[i];
    b[i] := b[j];
    b[j] := t;
    i := i + 1;
    j := j - 1;
  }
}
