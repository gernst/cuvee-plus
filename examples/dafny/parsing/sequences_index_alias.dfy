// ./Cuvee.sh -quiet examples/dafny/parsing/sequences_index_alias.dfy
type S = seq<int> function f(s: S): int { s[0] + |s| }
