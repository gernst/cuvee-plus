// the combinators of trace equation systems: trace, map, and all
function f(J: Seq<int>, a: [int]int, n: int): bool
{
  trace(0, for J do s, j => if j < n then s + a[j], if !(j < n) then s) == trace(0, for J do s, j => s)
  && all(for J check j => j < n)
}
