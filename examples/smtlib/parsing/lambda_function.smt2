; ./Cuvee.sh -quiet examples/smtlib/parsing/lambda_function.smt2
; lambdas are arrays also when function types are declared, since solvers support lambdas of array type only
(declare-const f (-> Int Int))
(assert (= f (lambda ((x Int)) x)))
