; lemmas and goals are written like assertions, with their own command
(declare-const x Int)
(assert (= x 1))
(lemma (< 0 x))
(goal (! (<= 1 x) :named positive))
(goal (par (a) (forall ((y a)) (= y y))))
