; assertions are normalized into clauses forall xs. antecedents ==> succedents after simplification, the antecedents are the context of the succedents
(declare-fun p (Int) Bool)
(declare-fun q (Int Int) Bool)
(declare-const r Bool)
(assert (forall ((x Int)) (=> (p x) (forall ((y Int)) (=> (q x y) (or r (not (p x))))))))
(assert (=> (exists ((x Int)) (and (p x) (not (or r (q x x))))) r))
(assert (not (and r (exists ((x Int)) (p x)))))
