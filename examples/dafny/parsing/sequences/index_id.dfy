// ./Cuvee.sh -print null examples/dafny/parsing/sequences/index_id.dfy
// indexing is resolved by overloading once the type of the base is known
function id<a>(x: a): a { x } function f(s: seq<int>): bool { id(s)[0] == s[1] }
