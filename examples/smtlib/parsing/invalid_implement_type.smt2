; ./Cuvee.sh -quiet examples/smtlib/parsing/invalid_implement_type.smt2
; the pattern of :implement has the result type of the implementation
(declare-fun twice (Int) Int)
(define-fun double ((x Int)) Bool (< 0 x) :implement (twice x))
