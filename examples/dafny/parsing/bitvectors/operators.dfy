// ./Cuvee.sh -print smt2 examples/dafny/parsing/bitvectors/operators.dfy
// the operators are resolved by overloading on the width
lemma forall x: bv8 :: x < x + 1
