; ./Cuvee.sh examples/smtlib/specs.smt2
; specifications in procedures, printed as assert, assume, havoc, and abort in these special cases, and spec otherwise

(define-proc p ((x Int)) ((y Int))
  (block
    (locals)
    (assert (< 0 x))
    (assume (< x 2))
    (havoc y)
    (spec (y) (< 0 x) (< x y))
    (abort)))
