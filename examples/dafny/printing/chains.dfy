// ./Cuvee.sh examples/dafny/printing/chains.dfy
// conjunctions of comparisons linked by their operands in one direction are chained,
// comparisons as operands of comparisons are parenthesized
function f(x: int, y: int, p: bool, q: bool, s: seq<int>): bool {
  (0 <= x && x < y) && (0 <= x && x < y && p) && (0 < x && y < x) && (0 < x && x > y) && ((x == y) == p)
}
