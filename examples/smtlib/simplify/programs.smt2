; ./Cuvee.sh -simplify examples/smtlib/simplify/programs.smt2
; programs are simplified statement by statement, each helper normalizes its own constructor
; assignments of variables to themselves and trivial specifications have no effect
(define-proc skip1 ((p Bool)) ((x Int) (y Int)) ()
  (assign (x x) (y 0)))
(define-proc skip2 ((p Bool)) ((x Int) (y Int)) ()
  (assign (x x)))
(define-proc skip3 ((p Bool)) ((x Int) (y Int)) ()
  (spec () true true))
; nested blocks are merged, also with locals, unless these capture variables of the other statements, unused locals are dropped
(define-proc blocks1 ((p Bool)) ((x Int) (y Int)) ()
  (sequence (assign (x (+ x 1))) (sequence (assign (x 0)) (assign (y y)))))
(define-proc blocks2 ((p Bool)) ((x Int) (y Int)) ()
  (sequence (sequence (assign (x (+ x 1))))))
(define-proc blocks3 ((p Bool)) ((x Int) (y Int)) ()
  (sequence (block (locals (z Int)) (assign (z x)) (assign (x z)))))
(define-proc blocks4 ((p Bool)) ((x Int) (y Int)) ()
  (block (locals (z Int)) (sequence (block (locals (z Int)) (assign (z x))) (assign (x z)))))
(define-proc blocks5 ((p Bool)) ((x Int) (y Int)) ()
  (block (locals (z Int)) (assign (x (+ x 1))) (assign (x 0))))
; statements after a jump are not reached
(define-proc jumps ((p Bool)) ((x Int) (y Int)) ()
  (while true (sequence (assign (x (+ x 1))) (break) (assign (x 0)))))
; constant tests select a branch, equal branches make the test irrelevant, negated tests swap the branches
(define-proc if1 ((p Bool)) ((x Int) (y Int)) ()
  (if true (assign (x (+ x 1))) (assign (x 0))))
(define-proc if2 ((p Bool)) ((x Int) (y Int)) ()
  (if (not true) (assign (x (+ x 1))) (assign (x 0))))
(define-proc if3 ((p Bool)) ((x Int) (y Int)) ()
  (if p (assign (x (+ x 1))) (assign (x (+ x 1)))))
(define-proc if4 ((p Bool)) ((x Int) (y Int)) ()
  (if (not p) (assign (x (+ x 1))) (assign (x 0))))
(define-proc while ((p Bool)) ((x Int) (y Int)) ()
  (while false (assign (x (+ x 1)))))
; nested choices are flattened, duplicates removed
(define-proc choice1 ((p Bool)) ((x Int) (y Int)) ()
  (choice (assign (x (+ x 1))) (choice (assign (x 0)) (assign (x (+ x 1))))))
(define-proc choice2 ((p Bool)) ((x Int) (y Int)) ()
  (choice (assign (x (+ x 1))) (assign (x (+ x 1)))))
