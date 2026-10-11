// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/first_duplicate.dfy
// whether a[0..n) has a duplicate, with an early exit of both loops by a flag that stops them (distinct.dfy runs
// all iterations); a search in a nested loop
//
// status: open; an attempt with -teq -simplify -split -simplify closed the goal, but also a wrong postcondition
// (r <==> distincts): the lemma distincts_flags, whose side condition is the summary r == !nodup(a, k, n) of the
// inner results as an invs, was applied although no such fact exists, since an invs side condition is matched in the
// simplifier's context of the fact's combinator (TODO.md on sum_invs_const), where the lemma nodup_distincts rewrote
// nodup(a, k, n) to true by the hypothesis distincts(...) of the split goal, which turned the condition into the
// constraint !r of the outer loop, a fact; removing nodup_distincts removes the unsound proof and leaves two goals;
// the lesson: a side condition that other rules can simplify under the conclusion to be proved is circular
// (NOTES.md); the approach otherwise: the summary of the inner loop as a rewrite of the fragment r == current(R) into
// r == !nodup(a, k, n), with the exit !(j < n && !r) of the early stop among the side conditions, then the outer trace
// is a trace of steps that do not depend on the previous value, whose current value is the last step
// (current_trace_last), and the two split goals are the exits by i == n (the last element has no later duplicate,
// and the flags of all iterations give distinctness) and by r (a duplicate contradicts distincts)

method main(a: array<int, int>, n: int) returns (r: bool)
  requires 0 <= n
  ensures r <==> !distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  r := false;
  i := 0;
  while i < n && !r
  {
    j := i + 1;
    while j < n && !r
    {
      if a[i] == a[j] {
        r := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
