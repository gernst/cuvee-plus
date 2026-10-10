// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/prefix_sums.dfy
// the prefix sums of a[0..n) in b: b[i] is the sum of a[0..i], computed from b[i - 1] with the two pointers k == i - 1
// and i, as the lemma current_trace_prefix_sums of teq.dfy expects them
//
// status: verified with -teq -simplify; the trace of b is the recurrence of current_trace_prefix_sums of teq.dfy
// with the added term a[i] at the written position i (teq.dfy has G(k) at the position k of the predecessor), hence
// the variant current_trace_prefix_sums_array; it reads the array directly, since the matcher instantiates a
// higher-order G(i) for a[i] by the array a itself (maps(... yield i :: a(i)) remained); its conditional includes
// the position 0, where the sum over no positions is 0 (sum_selects_zero), since the simplifier does not decide
// i == 0 from 0 <= i < 1 in the else branch; sum_selects_cons splits off the first position of the postcondition;
// the loop counter k₇ and the pointer k are two counters counter(0, 1, n) that the simplifier does not identify,
// so the trace has three dependencies, of which the pattern selects two

// an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus the element of
// a at its own position: current_trace_prefix_sums of teq.dfy with the added term at the written position i instead
// of k, and with the array read instead of a higher-order G(i), which the matcher instantiates by the array itself
lemma {:rw} current_trace_prefix_sums_array(b0: array<int, int>, a: array<int, int>, n: Nat, j: int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := a[i] + b[k]]))[j]
    == if 0 <= j <= integer(n) then b0[0] + sum(selects(a, ⌊counter(1, 1, natural(j))⌋)) else b0[j]

// the sum of the values at the positions i, ..., i + m is the first plus the sum of the rest
lemma {:rw} sum_selects_cons(a: array<int, int>, i: int, m: int)
  requires 0 <= m
  ensures sum(selects(a, ⌊counter(i, 1, natural(m + 1))⌋)) == a[i] + sum(selects(a, ⌊counter(i + 1, 1, natural(m))⌋))

// the sum over no positions
lemma {:rw} sum_selects_zero(a: array<int, int>, i: int, c: int)
  ensures sum(selects(a, ⌊counter(i, c, zero)⌋)) == 0

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 < n
  ensures forall i: int :: 0 <= i < n ==> b[i] == sum(selects(a, ⌊counter(0, 1, natural(i + 1))⌋))
{
  var i: int;
  var k: int;
  b := b[0 := a[0]];
  k := 0;
  i := 1;
  while i < n
  {
    b := b[i := b[k] + a[i]];
    k := k + 1;
    i := i + 1;
  }
}
