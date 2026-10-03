(declare-fun p (Int) Bool)

; the inner x must not be replaced by y via the equation on the outer x
(assert (forall ((x Int) (y Int)) (=> (= x y) (exists ((x Int)) (and (= x y) (p x))))))

; same for let
(assert (forall ((x Int) (y Int)) (=> (= x y) (let ((x 1)) (< x y)))))

; the bound expression of let is in the outer scope
(assert (forall ((x Int) (y Int)) (=> (= x y) (let ((x x)) (p x)))))

; shadowing an enclosing binder, the outer one becomes unused
(assert (forall ((x Int)) (forall ((x Int)) (p x))))

; no clash, no renaming
(assert (forall ((x Int)) (=> (p x) (exists ((z Int)) (and (p z) (< x z))))))
