// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/count_occurrences.dfy
// the number of occurrences of x in a[0..n), specified with the vocabulary of teq.dfy
//
// status: verified with -teq -simplify; the trace of c is counts over the reads at the counter, and the goal is
// c == count(x, selects(a, ⌊I⌋)) ==> c == count(x, selects(a, ⌊counter(0, 1, n')⌋)) with I == counter(0, 1, n'),
// which the simplifier does not close, since the counter I is not inlined into the facts; the lemma names the count
// over a counter, such that both sides normalize to the same term (the principle: name the normal form)

// the occurrences of x among the values of a at the positions of a counter, named, such that the postcondition and the
// trace equation system normalize to the same term, since the counter I of the loop is not inlined into the facts
function {:fold} occurrences(x: int, a: array<int, int>, i: int, n: int): int
{
  elems(selects(a, ⌊counter(i, 1, n)⌋))[x]
}

method main(a: array<int, int>, n: int, x: int) returns (c: int)
  requires 0 <= n
  ensures c == elems(selects(a, ⌊counter(0, 1, n)⌋))[x]
{
  var i: int;
  c := 0;
  i := 0;
  while i < n
  {
    if a[i] == x {
      c := c + 1;
    }
    i := i + 1;
  }
}
