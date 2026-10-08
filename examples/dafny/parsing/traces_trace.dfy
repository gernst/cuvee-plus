// ./Cuvee.sh -print null examples/dafny/parsing/traces_trace.dfy
type Trace<a₀>
const J: seq<int>
const B: seq<bool>
const n: int
axiom trace(0, for J do s, j :: s + j) == J
