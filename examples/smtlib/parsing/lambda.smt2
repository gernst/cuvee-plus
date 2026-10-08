; ./Cuvee.sh examples/smtlib/parsing/lambda.smt2
; lambdas are arrays of a single index
(assert (= (select (lambda ((x Int)) (+ x 1)) 0) 1))
