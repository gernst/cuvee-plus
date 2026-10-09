// ./Cuvee.sh -teq -simplify examples/dafny/sorting/nested_mult.dfy
// multiplication by repeated addition: the inner loop increments the outer variable n times
//
// status: open, like nested_sum.dfy; here the inner loop modifies the outer variable r, whose outer trace is the
// chain of the inner results, R == trace(0, for ⌊K⌋, R? do r, k, r' :: r') with r' == current(R') and
// R' == sums(r, maps(for ⌊K'⌋ yield 1)) in the fragments; what is needed is r' == r + n in each iteration, i.e.
// R == counter(0, n, m)

method main(m: int, n: int) returns (r: int)
  requires 0 <= m && 0 <= n
  ensures r == m * n
{
  var i: int;
  var j: int;
  r := 0;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      r := r + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
