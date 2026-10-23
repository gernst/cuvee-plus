; ./Cuvee.sh -prove examples/smtlib/prove/context.smt2
; subterms are simplified under the facts known at their position
(declare-const p Bool)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= (ite p (ite p x y) y) x))
(assert (=> (= x y) (= (f x) (f y))))
(assert (forall ((z Int)) (< x (+ y 1))))
(define-fun g ((z Int)) Int (ite (= z 0) z 0))
(assert (=> p (=> (not p) (< x y))))
(assert (not (and p (not p) (< x y))))
