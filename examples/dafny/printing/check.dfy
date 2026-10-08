// ./Cuvee.sh examples/dafny/printing/check.dfy
// check-sat is check, goals are parsed like lemmas, with attributes
const c: int
check
axiom c == 0
goal {:rw} forall x: int :: x < x + 1
