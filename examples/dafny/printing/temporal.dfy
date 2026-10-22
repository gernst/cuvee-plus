// ./Cuvee.sh examples/dafny/printing/temporal.dfy
// temporal operators: the unary ones take an operand down to the comparisons, the binary ones associate to the right
// and bind looser than the unary ones, but tighter than &&; parentheses only where needed
predicate prime(n: int)
predicate p()
predicate q()
predicate r()

goal forall x: int :: x >= 0 ==> always eventually prime(x)
goal forall x: int :: always (x >= 0) && x < 3 ==> next x >= 1
goal p() until q() until r()
goal (p() until q()) until r()
goal always p() until q()
goal always (p() until q())
goal !(always p()) <==> eventually !p()
goal p() unless+ q() || p() release+ q() && p() until+ q()
goal p() unless q() ==> p() release q()
goal (always p()) == q()
goal forall x: int :: ω₃(x) ==> next ω₃(x)
