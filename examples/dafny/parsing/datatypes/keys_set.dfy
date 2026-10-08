// ./Cuvee.sh -print null examples/dafny/parsing/datatypes/keys_set.dfy
// m.Keys and m.Values on other types than maps are rejected by type checking
function f(s: set<int>): set<int> { s.Keys }
