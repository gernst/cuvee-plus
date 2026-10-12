; ./Cuvee.sh -vcgen -z3 -verify examples/smtlib/verify/check_sat.smt2
; a check-sat of the input without :status is answered as in SMT-LIB and does not count; one with :status counts:
; the assertions are satisfiable against the expected status unsat, hence the answer at the end is incorrect,
; although the procedure is correct

(declare-const c Int)
(assert (< 0 c))

(define-proc p ((x Int)) ((y Int))
  (block
    (locals)
    (assign (y (+ x 1)))
    (assert (< x y))))

(check-sat)

(set-info :status unsat)
(check-sat)
