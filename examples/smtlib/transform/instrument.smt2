; ./Cuvee.sh -instrument examples/smtlib/transform/instrument.smt2
; -instrument: as -implement (implement.smt2), except that the procedure with a body (succ) is inlined
; instead of called, as a block whose locals are its formal parameters renamed apart, and dropped; the one with
; a contract only (between) is called
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
