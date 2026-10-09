// ./Cuvee.sh -print null examples/dafny/parsing/traces_typing.dfy
// type checking of the combinators trace, map, and all, the types of the bound variables are inferred from the dependencies
type Trace<a₀>
type List<a₀>
const J: List<int>
const B: List<bool>
const n: int
axiom trace(0, for J do s, j :: s + j) == trace(0, for J do s, j :: s + j)
axiom maps(for B yield x :: case x => 1 case !x => 0) == J
axiom maps(for J yield j :: case j < n => j case !(j < n) => n) == J
axiom invs(for J, B check j, q :: q || j < n)
