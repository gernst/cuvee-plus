; ./Cuvee.sh -vcgen -z3 -verify examples/smtlib/verify/check_sat.smt2
; a check-sat of the input counts like the one of -chc, it is expected sat (see pipe.Verify.expected): the assertions
; contradict each other, hence the answer is incorrect, although the procedure is correct

(declare-const c Int)
(assert (< 0 c))
(assert (< c 0))

(define-proc p ((x Int)) ((y Int)) ()
  (sequence
    (assign (y (+ x 1)))
    (assert (< x y))))

(check-sat)
