// decreases clauses on functions, predicates, methods, and loops,
// stored as :decreases attributes in order, one per component of the lexicographic measure
datatype list = nil() | cons(head: int, tail: list)

function len(xs: list): int
  decreases xs
{
  0
}

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
