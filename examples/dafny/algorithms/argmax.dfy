// ./Cuvee.sh -teq -entry main -prove examples/dafny/algorithms/argmax.dfy
// the position of a maximum of a[0..n), n > 0
//
// status: verified with -teq -simplify; the trace of the position is a selection, named argmaxs, whose cases bind by
// the update cover as incs and decs in bsearch.dfy, and whose current value is characterized by rules on the atoms of
// the postcondition: the bounds, and the read at the position as a bound of the other reads (the principle:
// selection traces have their facts as rules on the atoms that the postcondition states about their current value);
// the inner loop of selection sort is this loop, with argmin

// the trace of the position of the maximum so far, which moves to the positions of a counter whose value is larger
function argmaxs(a: array<int, int>, p0: int, i: int, n: Nat): Trace<int>

lemma {:rw} argmaxs_def(a: array<int, int>, p0: int, i: int, n: Nat)
  ensures trace(p0, for ⌊counter(0, 1, n)⌋, ⌊counter(i, 1, n)⌋ do p, k, j :: case a[p] < a[j] => j case a[j] <= a[p] => p)
    == argmaxs(a, p0, i, n)

// the final position is the initial one or one of the counter, hence within their bounds
lemma {:rw} current_argmaxs_lower(a: array<int, int>, p0: int, i: int, n: Nat, b: int)
  requires b <= p0 && b <= i
  ensures (b <= current(argmaxs(a, p0, i, n))) <==> true

lemma {:rw} current_argmaxs_upper(a: array<int, int>, p0: int, i: int, n: Nat, b: int)
  requires p0 < b && i + integer(n) <= b
  ensures (current(argmaxs(a, p0, i, n)) < b) <==> true

// and its value bounds the initial position and those of the counter
lemma {:rw} select_le_argmaxs(a: array<int, int>, p0: int, i: int, n: Nat, k: int)
  requires k == p0 || i <= k < i + integer(n)
  ensures (a[k] <= a[current(argmaxs(a, p0, i, n))]) <==> true

method main(a: array<int, int>, n: int) returns (p: int)
  requires 0 < n
  ensures 0 <= p < n
  ensures forall k: int :: 0 <= k < n ==> a[k] <= a[p]
{
  var i: int;
  p := 0;
  i := 1;
  while i < n
  {
    if a[p] < a[i] {
      p := i;
    }
    i := i + 1;
  }
}
