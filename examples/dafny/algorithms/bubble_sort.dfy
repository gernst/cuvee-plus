// ./Cuvee.sh -teq -include teq:sorted -include teq:aggregation -entry main -prove examples/dafny/algorithms/bubble_sort.dfy
// bubble sort with nested loops: the outer loop moves the bound i down, the inner loop swaps adjacent elements
// out of order below it
//
// status (Oct 14, 2026): verified with -teq -prove, both sorted(b, 0, n) and perm(b, a); a wrong postcondition,
// sorted(b, 0, n + 1) or perm(b, a[0 := 1]), leaves a goal;
// the inner loop is a value of the outer update, the trace of b over the counter, the numbers of inner iterations
// N? (a choice) and the counter of i, whose update is current(bubble_pass(b, ⌊counter(0, 1, nn)⌋)) once the fold
// below has applied; the constraints of the outer loop fix the length of each pass, which the engine states as
// maps(for ⌊K⌋, N? yield k, nn :: integer(nn) + k + 1) == ⌊consts(n', n)⌋; the induction sorted_bubbled_steps_choice
// ranges over the counter and the choice, takes that equation as a closed side condition (looked up among the
// facts), and decides its quantified step condition by bubbled_pass_nat; perm(b, a) follows from perm_steps_choice
// and perm_bubble_pass

// one pass of bubble sort over the positions js: adjacent elements out of order are swapped
function {:fold} bubble_pass(b: array<int, int>, js: List<int>): Trace<array<int, int>>
{
  trace(b, for js do x, j :: case x[j + 1] < x[j] => swap(x, j, j + 1) case x[j] <= x[j + 1] => x)
}

lemma {:rw} perm_bubble_pass(b: array<int, int>, c: array<int, int>, js: List<int>)
  ensures perm(current(bubble_pass(b, js)), c) <==> perm(b, c)

// the invariant of the outer loop after k passes: the suffix b[len - k..len) is sorted and all of b[0..len - k) are
// at most all of it, where the suffix is all of b[0..len) once k reaches len; a predicate indexed by the iteration,
// such that the induction below ranges over all iterations without a case distinction on k
function bubbled(b: array<int, int>, k: int, len: int): bool

// one pass over the positions 0, ..., nn - 1 for nn == len - k - 1 moves the maximum of b[0..nn] to nn, which extends
// the sorted suffix by one (for nn == 0 the pass is empty, and the suffix is the whole range already)
lemma {:rw} bubbled_pass_nat(b: array<int, int>, nn: int, k: int, len: int)
  requires nn == len - k - 1 && bubbled(b, k, len)
  ensures bubbled(current(bubble_pass(b, ⌊counter(0, 1, nn)⌋)), k + 1, len) <==> true

// the induction for bubble sort over a trace whose steps also read a choice ns, whose values the maps equation fixes
// to len - k - 1 in iteration k: the steps F keep the invariant from one iteration to the next, hence m steps sort
// b[0..len) if len <= m + 1 (the invariant holds initially by its definition, and every step is constrained, since
// the equation holds at every position of the choice)
lemma {:rw} sorted_bubbled_steps_choice(a: array<int, int>, len: int, m: int, ns: List<int>,
                                        F: (array<int, int>, int, int) -> array<int, int>)
  requires len <= m + 1
  requires maps(for ⌊counter(0, 1, m)⌋, ns yield k, nn :: nn + k + 1) == ⌊consts(m, len)⌋
  requires forall b: array<int, int>, k: int, nn: int ::
    0 <= k < m && nn + k + 1 == len && bubbled(b, k, len) ==> bubbled(F(b, k, nn), k + 1, len)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋, ns do b, k, nn :: F(b, k, nn))), 0, len) <==> true

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var j: int;
  var t: int;
  b := a;
  i := n;
  while 1 < i
  {
    j := 0;
    while j + 1 < i
    {
      if b[j + 1] < b[j] {
        t := b[j];
        b[j] := b[j + 1];
        b[j + 1] := t;
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
