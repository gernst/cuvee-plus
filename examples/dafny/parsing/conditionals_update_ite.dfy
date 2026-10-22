// ./Cuvee.sh -quiet examples/dafny/parsing/conditionals_update_ite.dfy
// the cases of updates begin with case, if-then-else expressions need no parentheses there
type Trace<a>
type List<a₀>
function f(J: List<int>): bool { trace(0, for J do s, j :: if j < 0 then s else s + 1) == trace(0, for J do s, j :: s) }
