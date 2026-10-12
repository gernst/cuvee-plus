; ./Cuvee.sh -split -z3 examples/smtlib/transform/split_named.smt2
; -split names the parts of a named assertion apart (f_def_1, f_def_2), since z3 rejects a name that is already
; defined: the axiom with if-then-else is split into its cases, the lemma into its conjuncts
(declare-fun f (Int) Int)

(assert (! (forall ((x Int)) (= (f x) (ite (> x 0) 1 0))) :named f_def))

(lemma (! (and (= (f 1) 1) (= (f 0) 0)) :named f_values))

(goal (= (f 2) 1))
