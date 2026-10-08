; ./Cuvee.sh -simplify -print null examples/smtlib/parsing/rewrite_invalid.smt2
; the variables of the right-hand side must occur in the left-hand side or the condition
(declare-fun f (Int) Int)
(assert (! (forall ((x Int) (y Int)) (= (f x) y)) :rw))
