// ./Cuvee.sh -teq -simplify -split -simplify examples/dafny/sorting/is_sorted.dfy
// whether a[0..n) is sorted, by a flag that is reset at a descent
//
// status: open, one goal remains: s == sorted(a, 0, n' + 1) && n == n' + 1 ==> s == sorted(a, 0, n), i.e. the
// simplifier does not substitute the solution n == n' + 1 of the exit into the argument of sorted (solutions of
// arithmetic equations are inlined into polynomials only, a bare variable as an argument is not replaced);
// what works: the flag is the trace of current_trace_flag of teq.dfy, which is typed int there and repeated here for
// booleans, hence s == if invs(no descent) then true else false, and the iteration constraint over the adjacent
// positions k and k + 1 is sorted(a, 0, n' + 1) by the definition lemma (the principle: flags are iteration
// constraints, iteration constraints over adjacent positions are the abstract predicate); the exit of the loop from 1
// is a disjunction with the case of no iteration, which -split separates only after a first -simplify produced it,
// hence the pipeline -simplify -split -simplify; the lemma exit_from_one is not needed with it
function sorted(a: array<int, int>, lo: int, hi: int): bool

// a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c:
// current_trace_flag of teq.dfy for booleans
lemma {:rw} current_trace_flag_bool(x0: bool, c: bool, n: Nat, hs: List<int>, D: (int, int) -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do f, k, h :: case D(k, h) => c case !D(k, h) => f))
    == if invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: !D(k, h)) then x0 else c

// no descent between the adjacent positions k and k + 1 for k below n means sorted up to n + 1
lemma {:rw} sorted_def(a: array<int, int>, n: Nat)
  ensures invs(for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ check k, i :: a[k] <= a[i]) <==> sorted(a, 0, integer(n) + 1)

// a range of at most one element is sorted
lemma {:rw} sorted_short(a: array<int, int>, lo: int, hi: int)
  requires hi <= lo + 1
  ensures sorted(a, lo, hi) <==> true

method main(a: array<int, int>, n: int) returns (s: bool)
  requires 0 <= n
  ensures s <==> sorted(a, 0, n)
{
  var i: int;
  s := true;
  i := 1;
  while i < n
  {
    if a[i] < a[i - 1] {
      s := false;
    }
    i := i + 1;
  }
}
