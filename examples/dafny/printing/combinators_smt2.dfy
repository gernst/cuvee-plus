// ./Cuvee.sh -print smt2 examples/dafny/printing/combinators_smt2.dfy
// the combinators of trace equation systems in SMT-LIB: trace, map, invs, and the cases of an update (eps),
// with the declarations of teq.dfy that they need, since they exist only with -teq otherwise,
// so that the output can be read back as SMT-LIB
type Trace<a₀>
type List<a₀>

function butlast<a₀>(x₀: Trace<a₀>): List<a₀>

function f(J: List<int>, a: array<int,int>, n: int): bool
{
  trace(0, for J do s, j :: case j < n => s + a[j] case !(j < n) => s) == trace(0, for J do s, j :: s)
  && invs(for J, maps(for J yield i :: i + 1) check j, k :: j < k)
}

function g(K: Trace<int>, n: int): bool
{
  invs(for ⌊K⌋ check k :: k < n)
}
