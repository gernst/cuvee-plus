; declarations, n-ary operators, annotations, push/pop

(set-logic ALL)
(set-option :produce-models true)

(declare-sort U 0)
(declare-const c U)
(declare-fun f (Int Int) Int)
(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))

(assert (= (f 1 2) (+ 1 2 3)))
(assert (! (< 0 1 2 3) :named chain))
(assert (distinct 1 2 3))
(assert (=> true true false false))
(assert (= (max 1 2) 2))
(assert (= c c))

; let binds in parallel: y refers to the outer x
(assert (forall ((x Int)) (let ((x (+ x 1)) (y x)) (< y x))))
(assert (let ((p (= c c)) (n (+ 1 2))) (ite p (< 0 n) false)))

(push 1)
(assert (forall ((x Int)) (exists ((y Int)) (and (< x y) (<= x y) (not (= x y))))))
(assert (= 2.5 0.25))
(check-sat)
(pop 1)
(check-sat)
(exit)
