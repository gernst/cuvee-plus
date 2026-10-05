; assertions are normalized into clauses forall xs. antecedents ==> succedents after simplification, the antecedents are the context of the succedents
(declare-fun p (Int) Bool)

(declare-fun q (Int Int) Bool)

(declare-fun r () Bool)

(assert
  (forall
    ((x Int) (y Int))
    (=> (and (p x) (q x y)) r)))

(assert
  (forall
    ((x Int))
    (=>
      (and (p x) (not (q x x)))
      r)))

(assert
  (forall ((x Int)) (not (and r (p x)))))

