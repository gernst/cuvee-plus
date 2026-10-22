; ./Cuvee.sh examples/smtlib/parsing/temporal.smt2
; temporal operators and placeholders, and functions of the same names, which take precedence
(declare-const p Bool)
(declare-const q Bool)
(declare-fun next (Int) Int)
(assert (until (always p) (eventually q)))
(assert (forall ((x Int)) (=> (|ω$3| x) (release+ (= (next x) 1) (|ω$3| x)))))
