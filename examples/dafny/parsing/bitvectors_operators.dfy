// ./Cuvee.sh -print smt2 examples/dafny/parsing/bitvectors_operators.dfy
// the operators are resolved by overloading on the width
lemma lemma_1(x: bv8)
  ensures x < x + 1
{}
