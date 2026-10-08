; ./Cuvee.sh examples/smtlib/functions.smt2
; function types and applications of SMT-LIB 2.7, (-> A B C) and (@ f a b), where @ is left-associative,
; (@ g 1 2) applies g to 1 and its result to 2
(declare-const f (-> Int Bool Int))
(declare-const g (-> Int (-> Int Int)))
(declare-fun h ((-> Int Int)) Int)
(assert (= (@ f 1 true) 2))
(assert (= (@ g 1 2) (@ (@ g 1) 2)))
(assert (= (h (@ g 3)) 0))
