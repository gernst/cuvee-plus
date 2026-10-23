// ./Cuvee.sh -quiet examples/dafny/parsing/invalid_implements_type.dfy
// the pattern has the result type of the implementation
function {:implements x in s} f(x: int, s: set<int>): int
