; ./Cuvee.sh -print dfy examples/smtlib/parsing/lambda_dafny.smt2
; lambdas are arrays, which Dafny cannot print
(assert (= (lambda ((x Int)) x) (lambda ((y Int)) y)))
