; ./Cuvee.sh -prove examples/smtlib/simplify/arith.smt2
; normal form of arithmetic as polynomials
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x 1) (+ 1 x)))
(assert (= (* (+ x 1) (- x 1)) y))
(assert (= (- x x) y))
(assert (= (div 7 2) 3))
(assert (= (mod (- 7) 2) 1))
(assert (= (div x 1) y))
(assert (> y x))
(assert (<= (+ x y) (+ y x)))
; comparisons are re-arranged so that both sides have positive coefficients only
(assert (<= (+ x 1) (- y x)))
(assert (< (- x y) (- 3)))
; on Int, < and <= absorb a summand 1
(assert (< x (+ y 1)))
(assert (<= (+ x y 1) (* 2 y)))
