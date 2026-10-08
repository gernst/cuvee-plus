; ./Cuvee.sh -simplify examples/smtlib/simplify/rewrite_conditions.smt2
; variables that occur only in the condition are instantiated by matching it against the facts of the context,
; the assumptions and the negated conclusions; closed conjuncts are decided first,
; and conjuncts without any instantiated variable are not searched
(declare-fun p (Int) Bool)
(declare-fun q (Int Int) Bool)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun f1 (Int) Int)
(declare-fun f2 (Int) Int)
(declare-fun f3 (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (! (forall ((x Int) (y Int)) (=> (q x y) (= (f x) (g y)))) :rw))
(assert (=> (q a b) (p (f a))))
(assert (=> (q a b) (p (f b))))
(assert (p (f a)))
(assert (! (forall ((x Int) (y Int)) (=> (not (q x y)) (= (f1 x) (g y)))) :rw))
(assert (or (q a b) (p (f1 a))))
(assert (! (forall ((x Int) (y Int)) (=> (and (<= 0 x) (q x y)) (= (f2 x) (g y)))) :rw))
(assert (=> (q a b) (p (f2 a))))
(assert (=> (and (q a b) (<= 0 a)) (p (f2 a))))
(assert (! (forall ((x Int) (y Int)) (=> (q y y) (= (f3 x) (g y)))) :rw))
(assert (=> (q b b) (p (f3 a))))
