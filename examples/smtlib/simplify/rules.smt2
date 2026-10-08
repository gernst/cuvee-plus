; ./Cuvee.sh -simplify examples/smtlib/simplify/rules.smt2
; rewrite rules are assertions and lemmas with the attribute :rw,
; whose universally quantified variables are the variables of the rule and whose premise is the condition
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-const a Int)
(assert (! (forall ((x Int)) (= (f (g x)) x)) :rw))
(assert (! (forall ((x Int)) (=> (<= 0 x) (p x))) :rw))
(lemma (! (forall ((x Int)) (not (q x))) :rw))
(assert (= (f (g (+ a 0))) a))
(assert (p 1))
(assert (=> (<= 0 a) (p a)))
(assert (p a))
(assert (q a))
