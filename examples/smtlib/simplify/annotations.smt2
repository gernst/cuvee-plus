; ./Cuvee.sh -prove examples/smtlib/simplify/annotations.smt2
; testers on constructor applications are evaluated, type annotations are kept
(declare-datatype Stack (par (a) ((nil) (cons (head a) (tail (Stack a))))))
(declare-const xs (Stack Int))
(assert ((_ is cons) (cons 1 xs)))
(assert ((_ is nil) (cons 1 xs)))
(assert ((_ is nil) (as nil (Stack Int))))
(assert ((_ is cons) xs))
(assert (= (as nil (Stack Int)) xs))
