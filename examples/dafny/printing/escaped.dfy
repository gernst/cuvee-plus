// ./Cuvee.sh examples/dafny/printing/escaped.dfy
// names that are neither identifiers nor operators are escaped by backticks, which the scanner reads back,
// e.g. the instances of Monomorph
function `f<Int>`(x: int): int
lemma lemma_1(x: int)
  ensures `f<Int>`(x) == x
{}
