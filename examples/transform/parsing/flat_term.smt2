; ./Cuvee.sh -flat -print null examples/transform/parsing/flat_term.smt2
(declare-datatype Pair ((pair (fst Int) (snd Int))))
(declare-fun x () Int)
(assert (= (fst (let ((y (pair x x))) y)) x))
