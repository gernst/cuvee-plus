; ./Cuvee.sh -flat -quiet examples/smtlib/parsing/flat_term.smt2
(declare-datatype Pair ((pair (fst Int) (snd Int))))
(declare-fun x () Int)
(assert (= (fst (let ((y (pair x x))) y)) x))
