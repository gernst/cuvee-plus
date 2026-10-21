; ./Cuvee.sh -print dfy examples/smtlib/printing/dafny_ode.smt2
; the evolution constraint follows while, the right hand sides need no parentheses
(define-proc m () ((x Real) (y Real)) ()
  (sequence
    (ode t ((x y) (y (- x))) true)
    (! (ode t ((x y)) (<= 0.0 x)) :invariant (<= x y))))
