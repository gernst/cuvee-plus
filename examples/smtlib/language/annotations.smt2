; ./Cuvee.sh examples/smtlib/language/annotations.smt2
; testers of constructors and explicit type annotations

(declare-datatype Stack (par (a) ((nil) (cons (head a) (tail (Stack a))))))

(declare-const xs (Stack Int))
(declare-const x Int)
(assert ((_ is cons) xs))
(assert (not ((_ is nil) (tail xs))))
(assert (= (as nil (Stack Int)) (tail (tail xs))))
(assert (= (as x Int) (head xs)))
(check-sat)
(exit)
