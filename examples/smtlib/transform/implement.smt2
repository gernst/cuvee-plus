; ./Cuvee.sh -implement examples/smtlib/transform/implement.smt2
; implementations named by :implement pattern, the implemented function applied to the inputs: a function replaces
; its function everywhere (twice by double), a procedure, with a contract or a body, replaces the applications in the
; expressions that programs execute by calls (some by between, other by succ); printing drops :implement of
; functions, whose declarations go to solvers
(declare-fun twice (Int) Int)
(define-fun double ((x Int)) Int (* 2 x) :implement (twice x))
(declare-fun some (Int Int) Int)
(declare-proc between ((lo Int) (hi Int)) ((x Int)) :implement (some lo hi) :requires (<= lo hi) :ensures (and (<= lo x) (<= x hi)))
(declare-fun other (Int) Int)
(define-proc succ ((y Int)) ((z Int)) () (! (sequence (assign (z (+ y 1)))) :implement (other y)))
(define-proc main ((n Int)) ((r Int)) ()
  (sequence
    (assign (r (twice n)))
    (assign (r (+ (some 0 r) (other r))))))
