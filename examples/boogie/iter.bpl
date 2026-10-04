// expected: valid
// nondeterministic iterations, while (*) { ... }, may stop after any number of iterations

var steps: int;

procedure walk(n: int) returns (k: int)
  requires 0 <= n;
  modifies steps;
  ensures 0 <= k && k <= n;
{
  k := 0;
  while (*)
    invariant 0 <= k && k <= n;
  {
    if (k < n) {
      k := k + 1;
    }
    steps := steps + 1;
  }
}
