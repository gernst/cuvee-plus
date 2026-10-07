// the combinators of trace equation systems: trace, map, and all,
// the type of traces is declared explicitly, since it exists only with -teq otherwise
type Trace<a>;

function f(J: Seq<int>, a: [int]int, n: int): bool
{
  trace(0, for J do s, j :: case j < n => s + a[j] case !(j < n) => s) == trace(0, for J do s, j :: s)
  && all(for J check j :: j < n)
}

// all but the last element of a trace, which is a sequence
function g(K: Trace<int>, n: int): bool
{
  all(for ⌊K⌋ check k :: k < n)
}

// lemmas on traces with type parameters, which are not monomorphized (see TODO.md)
function current<a>(X: Trace<a>): a;
function consts<a>(n: int, v: a): Trace<a>;

lemma <a> {:rw} (forall n: int, v: a :: 0 <= n ==> current(consts(n, v)) == v);
