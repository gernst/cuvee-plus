; ./Cuvee.sh -simplify examples/smtlib/simplify/clauses.smt2
; formulas are normalized into equivalent clauses forall xs. antecedents ==> succedents:
; nested implications and conjunctions among the antecedents are flattened, disjunctions among the succedents,
; negations move to the other side, existential antecedents and universal succedents bind their variables in the prefix,
; trivial clauses vanish, conjunctions among the succedents are kept
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (=> (and p q) (=> r (< x y))))
(assert (or (not (and p q)) r))
(assert (=> (not (or p q)) r))
(assert (=> (exists ((x Int)) (< x z)) (forall ((y Int)) (<= z y))))
(assert (=> false p))
(assert (or p true))
(assert (=> p (and q r)))
