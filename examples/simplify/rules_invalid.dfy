// ./Cuvee.sh -simplify -print null examples/simplify/rules_invalid.dfy
predicate p(x: int) axiom {:rw} forall x: int :: p(x) && p(x + 1)
