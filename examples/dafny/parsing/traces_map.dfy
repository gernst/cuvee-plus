// ./Cuvee.sh -print null examples/dafny/parsing/traces_map.dfy
type Trace<a₀>
type List<a₀>
const J: List<int>
const B: List<bool>
const n: int
axiom maps(for J yield j :: case j < n => j case !(j < n) => true) == J
