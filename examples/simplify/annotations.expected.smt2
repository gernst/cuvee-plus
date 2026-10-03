; testers on constructor applications are evaluated, type annotations are kept
(declare-datatype Stack (par (a) ((nil) (cons (head a) (tail (Stack a))))))
(declare-const xs (Stack Int))
(assert true)
(assert false)
(assert true)
(assert ((_ is cons) xs))
(assert (= (as nil (Stack Int)) xs))
