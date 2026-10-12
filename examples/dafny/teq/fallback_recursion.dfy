// ./Cuvee.sh -teq -entry recursion -fallback examples/dafny/teq/fallback_recursion.dfy
// the recursive definitions of teq.dfy by a match on a list or a natural, unfolded once per position: sum, count, and
// occurs over the list xs, a function of a position each, pow over the natural n, a function of the steps up to n

method recursion(xs: List<int>, x: int, n: Nat) returns (r: int)
  ensures 0 <= sum(xs) || occurs(x, xs)
  ensures count(x, xs) <= pow(2, n)
{
  r := 0;
}
