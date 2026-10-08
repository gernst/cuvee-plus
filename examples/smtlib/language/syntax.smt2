; ./Cuvee.sh examples/smtlib/language/syntax.smt2
(declare-fun abs (Int) Int
    :requires (lambda ((x Int)) (<= 0 x)))