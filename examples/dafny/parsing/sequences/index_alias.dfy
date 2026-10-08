// ./Cuvee.sh -print null examples/dafny/parsing/sequences/index_alias.dfy
type S = seq<int> function f(s: S): int { s[0] + |s| }
