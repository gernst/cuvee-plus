; ./Cuvee.sh -vcgen -z3 examples/smtlib/verify/check_sat.smt2
; a check-sat of the input is a query of its own, answered unsat, since the assertions contradict each other, and
; does not decide the program: the goal of the procedure is answered correct

(declare-const c Int)
(assert (< 0 c))
(assert (< c 0))

(define-proc p ((x Int)) ((y Int)) ()
  (sequence
    (assign (y (+ x 1)))
    (assert (< x y))))

(check-sat)
