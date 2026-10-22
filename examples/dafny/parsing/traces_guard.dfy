// ./Cuvee.sh -quiet examples/dafny/parsing/traces_guard.dfy
type Trace<a₀>
type List<a₀>
const J: List<int>
const B: List<bool>
const n: int
axiom trace(0, for J do s, j :: case j => s) == trace(0, for J do s, j :: s)
