; ./Cuvee.sh -prove examples/smtlib/prove/rewrite_nontermination_nested.smt2
; rules whose results grow exhaust the stack before the bound on the steps, which is reported in the same way
(declare-fun f (Int) Int)
(declare-fun p (Int) Bool)
(declare-const a Int)
(assert (! (forall ((x Int)) (= (f x) (f (f x)))) :rw))
(assert (p (f a)))
