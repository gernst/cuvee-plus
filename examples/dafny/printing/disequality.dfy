// ./Cuvee.sh examples/dafny/printing/disequality.dfy
// the parser reads a != b as !(a == b)
function f(x: int, y: int, p: bool, q: bool, s: seq<int>): bool {
  x != y && p != (x != y) && !(p && q)
}
