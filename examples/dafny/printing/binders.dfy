// ./Cuvee.sh examples/dafny/printing/binders.dfy
// binders inside of operators are parenthesized
function f(x: int, y: int, p: bool, q: bool, s: seq<int>): bool {
  (forall z: int :: z < y) && p
}
