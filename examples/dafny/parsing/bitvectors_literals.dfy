// ./Cuvee.sh -print smt2 examples/dafny/parsing/bitvectors_literals.dfy
// numeric literals take the type of their context, integers by default, and are reduced modulo 2^n
lemma lemma_1()
  ensures 1 + 2 == 3
{}
lemma lemma_2(x: bv8)
  ensures x != 300
{}
