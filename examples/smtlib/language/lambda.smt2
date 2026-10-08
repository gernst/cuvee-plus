; ./Cuvee.sh examples/smtlib/language/lambda.smt2
; lambdas of a single variable, which are arrays, applied with select
(declare-const n Int)
(define-fun shift () (Array Int Int) (lambda ((x Int)) (+ x n)))
(assert (= (select shift 1) (+ n 1)))
(assert (= (select (lambda ((b Bool)) (not b)) true) false))
(check-sat)
