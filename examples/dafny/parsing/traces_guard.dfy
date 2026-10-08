// ./Cuvee.sh -print null examples/dafny/parsing/traces_guard.dfy
type Trace<a₀>
const J: seq<int>
const B: seq<bool>
const n: int
axiom trace(0, for J do s, j :: case j => s) == trace(0, for J do s, j :: s)
