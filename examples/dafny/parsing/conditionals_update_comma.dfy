// ./Cuvee.sh -quiet examples/dafny/parsing/conditionals_update_comma.dfy
type Trace<a>
function f(J: seq<int>): bool { trace(0, for J do s, j :: if j < 0 then s, if 0 <= j then s + 1) == trace(0, for J do s, j :: s) }
