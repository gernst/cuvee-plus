; ./Cuvee.sh -monomorph examples/transform/mono.smt2
; polymorphic functions are replaced by their instances, also inside the definitions of other instances
(declare-sort Lst 1)
(declare-fun nil (par (a) () (Lst a)))
(declare-fun cons (par (a) (a (Lst a)) (Lst a)))
(define-fun single (par (a) ((x a)) (Lst a) (cons x (as nil (Lst a)))))
(declare-const b Bool)
(assert (= (single 1) (cons 1 (as nil (Lst Int)))))
(assert (= (single b) (single true)))
(check-sat)
