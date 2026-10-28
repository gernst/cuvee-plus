// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -entry recursion -fallback examples/dafny/teq/fallback_recursion.dfy
// the recursive definitions of teq.dfy by a match on a list or a test on an integer, unfolded once per position: sum,
// count, and occurs over the list xs, a function of a position each, pow over the integer n, a function of the steps
// up to n

method recursion(xs: List<int>, x: int, n: int) returns (r: int)
  ensures 0 <= sum(elems(xs)) || occurs(x, xs)
  ensures elems(xs)[x] <= pow(2, n)
{
  r := 0;
}
