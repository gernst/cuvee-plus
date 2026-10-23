// ./Cuvee.sh -teq -include teq:counters -include teq:sorted -entry main -prove -split -prove examples/dafny/algorithms/is_sorted.dfy
// whether a[0..n) is sorted, by a flag that is reset at a descent
//
// status: verified with the database alone (Oct 23, 2026; formerly with local copies of its lemmas): the flag is the
// trace of current_trace_flag of teq:counters, of any type, hence s == if invs(no descent) then true else false, and
// the iteration constraint over the adjacent positions k and k + 1 is sorted(a, 0, n' + 1) by sorted_adjacent of
// teq:sorted (the principle: flags are iteration constraints, iteration constraints over adjacent positions are the
// abstract predicate); a range of at most one element is sorted by sorted_short; the exit of the loop from 1 is a
// disjunction with the case of no iteration, which -split separates

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
