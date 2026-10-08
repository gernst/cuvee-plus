; ./Cuvee.sh -z3 examples/smtlib/solver/queries.smt2
; answers to get-info, get-option, labels, which are only available after check-sat, and get-model
(set-option :print-success true)
(set-option :produce-models true)
(declare-const x Int)
(get-info :name)
(get-info :foo)
(get-option :produce-models)
(check-sat)
(labels)
(assert (= x 1))
(check-sat)
(get-model)
