// ./Cuvee.sh -print null examples/dafny/parsing/sequences/seq.dfy
function f(s: seq<int>): bool { s[1..] + s[..1] == [s[0]] + s[1..|s|] }
