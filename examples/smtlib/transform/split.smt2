; ./Cuvee.sh -split examples/smtlib/transform/split.smt2
; -split splits goals into obligations: conjunctions are split, premises and bound variables move into the context,
; true is dropped, each obligation binds the variables that it uses, a succedent that is also an antecedent makes it true,
; disjunctions in the conclusion are succedents, negated conclusions antecedents, if-then-else in the terms of atoms
; is lifted and split by its test, disjunctions and if-then-else among the antecedents are split into cases,
; and existential quantifiers among the antecedents bind their variables
(declare-const y Int)
(declare-const p Bool)
(declare-const q Bool)
(goal (forall ((x Int)) (=> (and p true) (and (< x y) true (forall ((y Int)) (<= x y))))))
(goal (forall ((x Int) (z Int)) (=> p (< x x))))
(goal (forall ((x Int) (z Int)) (=> p p)))
(goal (=> false p))
(goal (or (not p) q))
(goal (< (ite p y 0) 0))
(goal (=> (or p q) (< 0 y)))
(goal (ite p q (< 0 y)))
(goal (=> (exists ((x Int)) (< x y)) (< 0 y)))
