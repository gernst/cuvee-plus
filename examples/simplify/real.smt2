; arithmetic on Real is normalized into polynomials with rational coefficients,
; division by a nonzero literal is multiplication by its inverse

(declare-const x Real)
(declare-const y Real)

(assert (= (- (* (+ x 0.5) 2.0) x) (+ x 1.0)))
(assert (= (/ (+ x x) 4.0) y))
(assert (< (* 3.0 (/ x 3.0)) (+ x (- y y))))
(assert (<= (/ 1.0 3.0) (+ (/ 1.0 6.0) (/ 1.0 6.0))))
(assert (> (/ x y) 0.0))
(assert (>= (- x) (* (- 1.0) x)))
(assert (< (- x 1.5) (* 2.0 y)))
