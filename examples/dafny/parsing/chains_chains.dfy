// ./Cuvee.sh -print smt2 examples/dafny/parsing/chains_chains.dfy
// chained comparisons are conjunctions, parenthesized comparisons do not chain
lemma lemma_1(i: int, j: int, n: int)
  ensures 0 <= i < n
{}
lemma lemma_2(i: int, j: int, n: int)
  ensures i == j == n
{}
lemma lemma_3(i: int, j: int, n: int)
  ensures i <= j == n < 1
{}
lemma lemma_4(i: int, j: int, b: bool)
  ensures (i == j) == b
{}
