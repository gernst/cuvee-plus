; ./Cuvee.sh -simplify examples/simplify/factor.smt2
; disjuncts common to all conjuncts and conjuncts common to all disjuncts are extracted
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(define-fun f1 () Bool (and (or a c) (or a b)))
(define-fun f2 () Bool (or (and a c) (and b a)))
(define-fun f3 () Bool (and (or a b c) (or c d a) (or a c)))
(define-fun f4 () Bool (and (or a b) (or c d)))
(define-fun f5 () Bool (or (and a b) (and a b c)))
