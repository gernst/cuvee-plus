// ./Cuvee.sh -print smt2 examples/dafny/parsing/bitvectors/conversions.dfy
// e as int and e as bv8 convert
lemma forall x: bv8 :: (x as int) < 256
lemma forall n: int :: ((n as bv8) as int) < 256
