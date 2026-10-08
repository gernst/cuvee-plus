// ./Cuvee.sh -print smt2 examples/dafny/parsing/chains/chains.dfy
// chained comparisons are conjunctions, parenthesized comparisons do not chain
lemma forall i: int, j: int, n: int :: 0 <= i < n
lemma forall i: int, j: int, n: int :: i == j == n
lemma forall i: int, j: int, n: int :: i <= j == n < 1
lemma forall i: int, j: int, b: bool :: (i == j) == b
