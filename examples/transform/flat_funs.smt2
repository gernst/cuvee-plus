; records in the signatures of functions, which are split by the fields of their results,
; constants of records, existential quantifiers, ite and distinct on records
(declare-datatype Pair (par (a b) ((pair (fst a) (snd b)))))
(declare-fun origin () (Pair Int Int))
(declare-fun step ((Pair Int Int)) (Pair Int Int))
(define-fun swap ((p (Pair Int Int))) (Pair Int Int) (pair (snd p) (fst p)))
(define-fun norm ((p (Pair Int (Pair Int Int)))) Int (+ (fst p) (fst (snd p)) (snd (snd p))))
(assert (= (fst origin) 0))
(assert (forall ((p (Pair Int Int))) (= (step p) (pair (+ (fst p) 1) (snd p)))))
(assert (exists ((p (Pair Int Int)) (b Bool))
  (and (= (swap p) (ite b origin (step origin))) (distinct p origin))))
(assert (= (norm (pair 1 (swap origin))) 1))
(check-sat)
