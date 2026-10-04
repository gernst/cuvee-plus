// the combinators of trace equation systems: trace, map, and all
function f(J: seq<int>, a: array<int,int>, n: int): bool
{
  trace(0, for J do s, j => s + a[j]) == trace(0, for J do s, j => if j < n then s + 1, if !(j < n) then s)
  && all(for J, map(for J yield i => i + 1) check j, k => j < k)
  && trace(0, for J do s, j => if j < n then s else s + 1) == trace(0, for J do s, j => s)
}

// all but the last element of a trace, which is a sequence
function g(K: Trace<int>, n: int): bool
{
  all(for ⌊K⌋ check k => k < n)
}
