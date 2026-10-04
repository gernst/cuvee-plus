// the combinators of trace equation systems: trace, map, and all
function f(J: Seq<int>, a: [int]int, n: int): bool
{
  trace(0, for J do s, j => if j < n then s + a[j], if !(j < n) then s) == trace(0, for J do s, j => s)
  && all(for J check j => j < n)
}

// all but the last element of a trace, which is a sequence
function g(K: Trace<int>, n: int): bool
{
  all(for ⌊K⌋ check k => k < n)
}
