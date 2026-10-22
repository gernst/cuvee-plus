// ./Cuvee.sh -quiet examples/dafny/parsing/sequences_constant.dfy
// the type of a polymorphic constant is determined by an overloaded operator to its right
function c<a>(): a function f(s: seq<int>): bool { c() + c() == s[0] }
