// ./Cuvee.sh -teq -simplify -split -simplify examples/dafny/algorithms/reverse.dfy
// the reversal of a[0..n) in place, with two pointers i and j that move towards each other
//
// status: verified with -teq -simplify -split -simplify; the two-pointer form makes the positions of the swaps
// counters, ⌊counter(0, 1, n')⌋ and ⌊counter(n - 1, -1, n')⌋, which the lemma on the trace of the swaps matches,
// whereas the form with one pointer swaps b[i] and b[n - 1 - i], arithmetic on the bound variable of the trace, which
// patterns do not match (TODO.md); the lemmas: the loop test i < j is the iteration constraint 2 k + 1 < n, which the
// lemmas of teq.dfy on bounds of counters do not resolve (invs_pairs); the exit is n <= integer(n') + i + 1 with
// i == integer(n') kept as a definition, which the simplifier follows on demand but does not substitute into the
// arithmetic facts, hence exit_pointers; the trace of the swaps is characterized for the complete reversal, as the
// exit gives it, such that the middle element of an odd range needs no case of its own; the literal -1 in a pattern
// is not matched, hence the step of the counter down is a variable with a side condition; -split separates the
// case of no iteration from the disjunction that invs_pairs leaves, after the first -simplify produced it
// of the swaps are counters, not arithmetic on the iteration, which patterns do not match

// the loop test i < j of the two pointers, as an iteration constraint over the counter: twice the iterations stay
// below the length, i.e. the pairs are disjoint; the lemmas of teq.dfy resolve bounds on the counter itself only
lemma {:rw} invs_pairs(n: Nat, m: int, hs: List<int>, gs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, gs check k, h, g :: 2 * k + 1 < m)
    <==> n == zero || 2 * integer(n) - 1 < m

// the exit i < j of the two pointers, where i is the current value of the counter, i == integer(n), which the
// simplifier records as a definition that is followed on demand only, not substituted into the arithmetic facts
lemma {:rw} exit_pointers(m: int, n: Nat, i: int)
  requires i == integer(n)
  ensures (m <= integer(n) + i + 1) <==> (m <= 2 * integer(n) + 1)

// the trace of the swaps of the positions k and c - k for k below n, with 2 n == c + 1 or 2 n == c, i.e. all pairs
// of a[0..c] except for a middle element: the current array is a reversed at 0..c and unchanged elsewhere; stated for
// the complete reversal, as the exit of the loop gives it, such that the middle element needs no case of its own;
// the step of the counter down is a variable d with d == -1 as a side condition, since the literal -1 in a pattern
// is not matched
lemma {:rw} current_reversal(a: array<int, int>, c: int, d: int, n: Nat, j: int)
  requires 2 * integer(n) <= c + 1 && c <= 2 * integer(n) && d == -1
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
