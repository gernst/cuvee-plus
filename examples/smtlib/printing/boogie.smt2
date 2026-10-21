; ./Cuvee.sh -print bpl examples/smtlib/printing/boogie.smt2
; what only SMT-LIB writes, printed in Boogie: distinct of several arguments, chained comparisons,
; let, which is substituted, and specifications as assert, havoc, and assume
(declare-const x Int)
(declare-const y Int)
(assert (distinct x y))
(assert (distinct x y 0))
(assert (< x y 0))
(assert (= (let ((x y)) (+ x x)) 0))
(define-proc m () ((a Int) (b Int)) ()
  (spec (a) (< 0 a) (< a b)))
