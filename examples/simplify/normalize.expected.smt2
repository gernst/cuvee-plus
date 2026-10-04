; assertions are normalized into clauses forall xs. antecedents ==> succedents before and after simplification
(declare-fun p (Int) Bool)

(declare-fun q (Int Int) Bool)

(declare-fun r () Bool)

(assert
  (forall
    ((x Int) (y Int))
    (=> (and (q x y) (p x)) r)))

(assert
  (forall
    ((x Int))
    (=> (p x) (or (q x x) r))))

(assert
  (forall ((x Int)) (not (and r (p x)))))

