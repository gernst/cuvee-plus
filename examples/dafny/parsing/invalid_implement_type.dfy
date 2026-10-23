// ./Cuvee.sh -quiet examples/dafny/parsing/invalid_implement_type.dfy
// the pattern has the result type of the implementation
function {:implement x in s} f(x: int, s: set<int>): int
