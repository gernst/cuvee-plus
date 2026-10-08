// ./Cuvee.sh examples/dafny/printing/escaped.dfy
// names that are neither identifiers nor operators are escaped by backticks, which the scanner reads back,
// e.g. the instances of Monomorph
function `f<Int>`(x: int): int
lemma forall x: int :: `f<Int>`(x) == x
