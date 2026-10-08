// ./Cuvee.sh -print smt2 examples/dafny/parsing/bitvectors/literals.dfy
// numeric literals take the type of their context, integers by default, and are reduced modulo 2^n
lemma 1 + 2 == 3
lemma forall x: bv8 :: x != 300
