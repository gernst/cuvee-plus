; arithmetic and comparison are overloaded for Int and Real,
; resolved by the type of the arguments after type checking

(declare-const a Real)
(declare-const n Int)

(assert (< (+ a 0.5) (/ 1.0 3.0)))
(assert (<= (* 2.0 a) (- a)))
(assert (< (+ n 1) (div n 2)))
(check-sat)
