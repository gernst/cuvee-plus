// the combinators of trace equation systems: trace, map, and all,
// the type of traces is declared explicitly, since it exists only with -teq otherwise
type Trace<a>

function f(J: seq<int>, a: array<int,int>, n: int): bool
{
  trace(0, for J do s, j :: s + a[j]) == trace(0, for J do s, j :: case j < n => s + 1 case !(j < n) => s)
  && invs(for J, maps(for J yield i :: i + 1) check j, k :: j < k)
  && trace(0, for J do s, j :: (if j < n then s else s + 1)) == trace(0, for J do s, j :: s)
}

// all but the last element of a trace, which is a sequence
function g(K: Trace<int>, n: int): bool
{
  invs(for ⌊K⌋ check k :: k < n)
}
