; ./Cuvee.sh -flat examples/smtlib/transform/flat.smt2
; records, also generic and nested ones, are flattened in the arguments of predicates,
; recursive datatypes and those with several constructors are not
(set-logic HORN)
(declare-datatype Pair (par (a b) ((pair (fst a) (snd b)))))
(declare-datatype Stack (par (a) ((nil) (cons (head a) (tail (Stack a))))))
(declare-fun p ((Pair Int (Pair Int Bool)) (Stack Int)) Bool)
(assert (forall ((x (Pair Int (Pair Int Bool))) (s (Stack Int)))
  (=> (and (= (fst x) 0) (snd (snd x)) ((_ is pair) x)) (p x s))))
(assert (forall ((x (Pair Int (Pair Int Bool))) (y (Pair Int (Pair Int Bool))) (s (Stack Int)))
  (=> (and (p x s) (= y (pair (+ (fst x) 1) (snd x)))) (p y (cons (fst y) s)))))
(assert (forall ((x (Pair Int (Pair Int Bool))) (s (Stack Int)))
  (=> (and (p x s) (< (fst x) 0)) false)))
(check-sat)
