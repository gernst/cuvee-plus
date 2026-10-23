; ./Cuvee.sh -prove examples/smtlib/simplify/rewrite_equations.smt2
; equations match in either orientation
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (! (forall ((x Int) (y Int)) (= (= (f x) y) false)) :rw))
(assert (not (= (f a) b)))
(assert (not (= b (f a))))
(assert (not (= a b)))
