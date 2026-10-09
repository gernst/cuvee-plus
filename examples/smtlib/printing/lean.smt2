; ./Cuvee.sh -print lean examples/smtlib/printing/lean.smt2
; SMT-LIB in Lean 4: the commands without a counterpart are comments, the selectors of SMT-LIB are not qualified,
; the variables of let are bound in parallel, comparisons of numerals are annotated with their type
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((Stack 1)) ((par (a) ((nil) (cons (top a) (pop (Stack a)))))))
(declare-fun c () U)
(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))
(assert (! (forall ((x Int)) (let ((x (+ x 1)) (y x)) (< y x))) :named shift))
(assert (and (< 0 1) (= 2.5 0.25) (distinct 1 2 3)))
(assert (= (top (cons c nil)) c))
(push 1)
(check-sat)
(pop 1)
