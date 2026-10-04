; subterms are simplified under the facts known at their position
(declare-const p Bool)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= (ite p x y) x))
(assert (=> (= x y) (= (f x) (f y))))
(assert (<= x y))
(define-fun g ((z Int)) Int (ite (= z 0) z 0))
