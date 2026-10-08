; ./Cuvee.sh examples/smtlib/parsing/functions.smt2
; function types (-> A B C) and applications (@ f a b) of SMT-LIB 2.7,
; a function of fewer arguments is applied to the first ones, and its result to the rest
(declare-const f (-> Int Bool Int))
(assert (= (@ f 1 true) 2))
(declare-const g (-> Int (-> Int Int)))
(assert (= (@ g 1 2) 0))
