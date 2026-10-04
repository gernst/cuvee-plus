; normal form of arithmetic as polynomials
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* x x) (- 1)) y))
(assert (= 0 y))
(assert (= x y))
(assert (< x y))
(assert (<= (+ (* 2 x) 1) y))
(assert (< (+ x 3) y))
