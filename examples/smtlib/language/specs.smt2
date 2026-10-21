; ./Cuvee.sh examples/smtlib/language/specs.smt2
; specifications in procedures, printed as assert, assume, havoc, and abort in these special cases, and spec otherwise

(define-proc p ((x Int)) ((y Int)) ()
  (sequence
    (assert (< 0 x))
    (assume (< x 2))
    (havoc y)
    (spec (y) (< 0 x) (< x y))
    (abort)))
