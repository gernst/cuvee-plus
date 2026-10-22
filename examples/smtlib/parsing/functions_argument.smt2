; ./Cuvee.sh -quiet examples/smtlib/parsing/functions_argument.smt2
(declare-const f (-> Int Int))
(assert (= (@ f true) 0))
