// ./Cuvee.sh examples/dafny/printing/datatypes.dfy
// testers on variables, annotations bind tighter than operators but are no operands of accesses
datatype list = nil | cons(head: int, tail: list)
function f(xs: list, s: seq<int>): bool { xs.nil? && [] as seq<int> + s == s && (s as seq<int>)[0] == 0 }
