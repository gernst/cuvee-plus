// ./Cuvee.sh -teq -simplify examples/dafny/sorting/nested_counter.dfy
// the simplest nested loop: the inner loop counts to n and has no effect on the outer variable
//
// status: verified with -teq -simplify; the inner loop's trace equations become iteration constraints of the outer
// loop over fresh sequences, which are unused for the goal i == m

method main(m: int, n: int) returns (i: int)
  requires 0 <= m && 0 <= n
  ensures i == m
{
  var j: int;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      j := j + 1;
    }
    i := i + 1;
  }
}
