// ./Cuvee.sh -quiet examples/dafny/parsing/conditionals_update_cases.dfy
type Trace<a>
type List<a₀>
function f(J: List<int>): bool { trace(0, for J do s, j :: case j < 0 => s case 0 <= j => s + 1) == trace(0, for J do s, j :: s) }
