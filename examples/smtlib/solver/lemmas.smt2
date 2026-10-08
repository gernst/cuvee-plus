; ./Cuvee.sh -z3 examples/smtlib/solver/lemmas.smt2
; lemmas and goals are proved, lemmas are asserted subsequently, free lemmas are assumed without proof,
; and goals follow from axioms
(declare-const x Int)
(lemma (= x x))
(lemma (! (= x 1) :free))
(goal (< 0 x))
(push 1)
(assert (= x 1))
(lemma (< 0 x))
(goal (< 0 x))
(pop 1)
