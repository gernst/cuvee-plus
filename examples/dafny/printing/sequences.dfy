// ./Cuvee.sh examples/dafny/printing/sequences.dfy
// sequence literals are concatenations of units, + and <= are overloaded, x in s is containment of [x]
function f(x: int, y: int, p: bool, q: bool, s: seq<int>): bool {
  [] == s && [x, y] == s && s + [x] == s && [x] <= s && x in s && |s| == 0 && s[0] == x && s[0 := x] == s && s[1..x - 1] == s && s[0..x] == s
}
