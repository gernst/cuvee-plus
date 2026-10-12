// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/iter.dfy
// expected: valid
// nondeterministic iterations, while * { ... }, may stop after any number of iterations,
// the body may leave the loop by break as well

method bounded(n: int) returns (k: int)
  requires 0 <= n
  ensures 0 <= k && k <= n
{
  k := 0;
  while *
    invariant 0 <= k && k <= n
  {
    if k == n {
      break;
    }
    k := k + 1;
  }
}
