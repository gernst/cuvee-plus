// ./Cuvee.sh -print null examples/dafny/parsing/sequences_index_update.dfy
function f(s: seq<bool>, i: int, j: int): bool { s[i] == s[j] && s[i := s[j]] == s }
