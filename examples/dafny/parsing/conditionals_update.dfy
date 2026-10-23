// ./Cuvee.sh examples/dafny/parsing/conditionals_update.dfy
// the guarded cases of updates begin with case, if-then-else expressions need no parentheses there
type Trace<a>
type List<a₀>
function cases(J: List<int>): bool { trace(0, for J do s, j :: case j < 0 => s case 0 <= j => s + 1) == trace(0, for J do s, j :: s) }
function ite(J: List<int>): bool { trace(0, for J do s, j :: if j < 0 then s else s + 1) == trace(0, for J do s, j :: s) }
