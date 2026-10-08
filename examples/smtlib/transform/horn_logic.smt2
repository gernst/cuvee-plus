; ./Cuvee.sh -chc examples/smtlib/transform/horn_logic.smt2
; -chc sets the logic at the beginning, a given logic is replaced, not duplicated
(set-logic ALL)
(declare-const x Int)
(assert (= x 0))
