// ./Cuvee.sh -simplify -quiet examples/dafny/simplify/rules_invalid.dfy
predicate p(x: int) axiom {:rw} forall x: int :: p(x) && p(x + 1)
