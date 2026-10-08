; ./Cuvee.sh examples/smtlib/printing/functions.smt2
; function types and applications are printed as in SMT-LIB 2.7
(declare-const f (-> Int Bool Int))
(assert (= (@ f 1 true) 2))
