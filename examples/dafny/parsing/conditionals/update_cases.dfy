// ./Cuvee.sh -print null examples/dafny/parsing/conditionals/update_cases.dfy
type Trace<a>
function f(J: seq<int>): bool { trace(0, for J do s, j :: case j < 0 => s case 0 <= j => s + 1) == trace(0, for J do s, j :: s) }
