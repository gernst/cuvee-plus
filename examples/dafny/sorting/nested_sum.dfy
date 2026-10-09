// ./Cuvee.sh -teq -simplify examples/dafny/sorting/nested_sum.dfy
// the result of the inner loop is used once per outer iteration: c is the sum of m times n
//
// status: open; the goal that remains has c == sum(J?) for the sequence J? of the final values j of the inner loop,
// whose facts are fragments of the iteration constraint of the outer loop (see invs_counter_equation.dfy and
// invs_fragments.dfy): J == sums(0, maps(for ⌊K⌋ yield 1)) is not recognized as counter(0, 1, n'), since the equation
// K == counter(0, 1, n') of the same iteration is not followed, and j == current(J), invs(for ⌊J⌋ check j :: j < n),
// and n <= j are separate fragments; what is needed is j == n in each iteration, i.e. J? == ⌊consts(m, n)⌋, and then
// sum_consts

method main(m: int, n: int) returns (c: int)
  requires 0 <= m && 0 <= n
  ensures c == m * n
{
  var i: int;
  var j: int;
  c := 0;
  i := 0;
  while i < m
  {
    j := 0;
    while j < n
    {
      j := j + 1;
    }
    c := c + j;
    i := i + 1;
  }
}
