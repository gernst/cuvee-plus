// ./Cuvee.sh -prove -quiet examples/dafny/prove/rules_invalid.dfy
predicate p(x: int) axiom {:rw} forall x: int :: p(x) && p(x + 1)
