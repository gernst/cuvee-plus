; ./Cuvee.sh -flat -quiet examples/smtlib/parsing/flat_parameter.smt2
; unsupported: records that instantiate type parameters, also of arrays, and other terms of records
(declare-datatype Pair ((pair (fst Int) (snd Int))))
(declare-fun p (par (a) (a) Bool))
(assert (forall ((x Pair)) (p x)))
