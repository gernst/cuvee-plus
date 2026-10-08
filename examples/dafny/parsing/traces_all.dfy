// ./Cuvee.sh -print null examples/dafny/parsing/traces_all.dfy
type Trace<a₀>
const J: seq<int>
const B: seq<bool>
const n: int
axiom invs(for J check j :: j)
