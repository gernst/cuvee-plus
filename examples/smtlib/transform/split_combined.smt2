; ./Cuvee.sh -split -z3 examples/smtlib/transform/split_combined.smt2
; each goal has one answer, combined from those of its parts (Stage.combine): the first goal splits into two valid
; parts and is correct, the second into a valid and a refuted part and is incorrect
(declare-const x Int)
(goal (and (= x x) (<= x x)))
(goal (and (= x x) (< x x)))
