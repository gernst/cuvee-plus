; ./Cuvee.sh examples/smtlib/language/sorts.smt2
; defined sorts are unfolded during type checking,
; also when the definition does not use all parameters
(define-sort Set (T) (Array T Bool))
(define-sort Ignore (T) Int)

(declare-const s (Set Int))
(declare-const t (Array Int Bool))
(declare-const i (Ignore Bool))

(assert (select s 1))
(assert (= s t))
(assert (= i (+ i 1)))
