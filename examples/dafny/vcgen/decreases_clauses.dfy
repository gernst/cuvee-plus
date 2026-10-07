// expected: valid
// decreases clauses on predicates, methods, and loops,
// stored as :decreases attributes in order, one per component of the lexicographic measure
predicate pos(n: int)
  requires 0 <= n
  decreases n

method count(n: int) returns (k: int)
  requires 0 <= n
  ensures k == n
  decreases n, 0
{
  k := 0;
  while k < n
    invariant k <= n
    decreases n - k
  {
    k := k + 1;
  }
}
