; ./Cuvee.sh -simplify examples/smtlib/simplify/rewrite_nontermination.smt2
; the number of steps of the rewrite rules is bounded
(declare-fun f (Int) Int)
(declare-fun p (Int) Bool)
(declare-const a Int)
(assert (! (forall ((x Int)) (= (f x) (f (+ x 1)))) :rw))
(assert (p (f a)))
