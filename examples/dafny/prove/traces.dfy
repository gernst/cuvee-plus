// ./Cuvee.sh -prove examples/dafny/prove/traces.dfy
// the combinators of trace equation systems: guards and results are simplified, cases with guard false are dropped,
// results are simplified under their guard, and all is true if its body is;
// dependencies whose bound variables are unused are dropped, except the first one if none remains,
// and equal dependencies are collapsed
type Trace<a₀>
type List<a₀>
function f(x: int): int
const J: List<int>
const K: List<int>
const n: int
axiom trace(0, for J do s, j :: case j < n => s + 2 * j - j case j < n && !(j < n) => s case !(j < n) => (if j < n then 1 else s))
  == trace(0, for J do s, j :: s + 0)
axiom invs(for J check j :: j < n ==> j < n || f(j) == 0)
axiom maps(for J yield j :: j + 1 - 1) == J
axiom invs(for K, J, J check k, j, i :: i + j < n)
axiom invs(for K, J check k, j :: 0 < n)
