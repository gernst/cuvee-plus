; ./Cuvee.sh -flat -quiet examples/smtlib/parsing/flat_array.smt2
(declare-datatype Pair ((pair (fst Int) (snd Int))))
(declare-fun a () (Array Int Pair))
(assert (forall ((x Pair)) (= (store a 0 x) a)))
