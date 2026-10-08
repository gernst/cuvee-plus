// ./Cuvee.sh -print null examples/dafny/parsing/traces_map.dfy
type Trace<a₀>
const J: seq<int>
const B: seq<bool>
const n: int
axiom maps(for J yield j :: case j < n => j case !(j < n) => true) == J
