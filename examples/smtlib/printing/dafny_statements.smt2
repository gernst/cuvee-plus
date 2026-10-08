; ./Cuvee.sh -print dfy examples/smtlib/printing/dafny_statements.smt2
; statements in Dafny: parallel assignments, specifications, choices, else if, and loops without test
(define-proc m ((x Int) (y Int)) ((a Int) (b Int))
  (block (locals)
    (assign (a y) (b x))
    (assume (< a b))
    (havoc a b)
    (spec (a) (< 0 a) (< a b))
    (choose (assign (a 0)) (assign (a y)))
    (while true (if (< x y) (break) (if (< y x) (continue) (block (locals)))))
    (iter (assign (a y)) :invariant (<= a y))))
