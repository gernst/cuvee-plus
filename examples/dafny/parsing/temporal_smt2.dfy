// ./Cuvee.sh -print smt2 examples/dafny/parsing/temporal_smt2.dfy
// temporal operators are applications in SMT-LIB, placeholders quoted symbols
predicate p()
predicate q()

goal forall x: int :: always x >= 0 && x < 3 ==> next x >= 1 until p()
goal always p() until+ q()
goal forall x: int :: ω₃(x) ==> eventually ω₃(x)
