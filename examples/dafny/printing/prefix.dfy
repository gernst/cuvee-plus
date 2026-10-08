// ./Cuvee.sh examples/dafny/printing/prefix.dfy
// prefix operators
function f(x: int, y: int, p: bool, q: bool, s: seq<int>): bool {
  !(p && q) && (!p && q) && (!p == q) && -(-x) == -x + y
}
