; ./Cuvee.sh -print null examples/smtlib/parsing/lambda_several.smt2
; multi-index arrays of SMT-LIB are not curried, unlike the maps of several indices of Boogie
(assert (= (lambda ((x Int) (y Int)) x) (lambda ((x Int) (y Int)) y)))
