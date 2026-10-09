// ./Cuvee.sh -monomorph examples/dafny/transform/mono_combinators.dfy
// polymorphic functions are replaced by their instances also inside the combinators of trace equation systems
type Lst<a>
type List<a₀>
function single<a>(x: a): Lst<a>
const J: List<int>
axiom maps(for J yield j :: single(j)) == maps(for J yield j :: single(j + 0))
