// ./Cuvee.sh -quiet examples/dafny/parsing/traces_all.dfy
type Trace<a₀>
type List<a₀>
const J: List<int>
const B: List<bool>
const n: int
axiom invs(for J check j :: j)
