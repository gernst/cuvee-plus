; ./Cuvee.sh -prove examples/smtlib/prove/rewrite.smt2
; rewrite rules are applied after each round of simplification, their results are simplified further,
; terms under test are arguments of the uninterpreted predicate p, which the simplifier only traverses
(declare-fun p (Int) Bool)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)
(declare-fun k (Int) Int)
(declare-fun l (Int) Int)
(declare-fun abs (Int) Int)
(declare-fun m (Int) Int)
(declare-const a Int)
(declare-const b Int)
; the argument is simplified first, then the rule applies to the result
(assert (! (forall ((x Int)) (= (f (g x)) x)) :rw))
(assert (p (f (g (+ a 0)))))
; the variables of a rule are instantiated consistently
(assert (! (forall ((x Int)) (= (h x x) 0)) :rw))
(assert (p (h a a)))
(assert (p (h a b)))
; the first rule that applies is used
(assert (! (forall ((x Int)) (= (k x) (l x))) :rw))
(assert (! (forall ((x Int)) (= (k x) x)) :rw))
(assert (p (k a)))
; conditions are decided by the simplifier, also from the context
(assert (! (forall ((x Int)) (=> (<= 0 x) (= (abs x) x))) :rw))
(assert (p (abs 1)))
(assert (p (abs a)))
(assert (=> (<= 0 a) (p (abs a))))
; variables of the rule match bound variables of the expression
(assert (forall ((c Int)) (p (f (g c)))))
; constants of a rule are not instantiated
(assert (! (= (m a) b) :rw))
(assert (p (m a)))
(assert (p (m b)))
