// ./Cuvee.sh -print smt2 examples/dafny/parsing/bitvectors_conversions.dfy
// e as int and e as bv8 convert
lemma lemma_1(x: bv8)
  ensures (x as int) < 256
{}
lemma lemma_2(n: int)
  ensures ((n as bv8) as int) < 256
{}
