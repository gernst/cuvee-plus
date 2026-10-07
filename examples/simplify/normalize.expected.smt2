; assertions are normalized into clauses forall xs. antecedents ==> succedents before and after each round of simplification, the antecedents are the context of the succedents, let is turned into equations
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

(assert
  (forall
    ((y Int) (x$1 Int))
    (=>
      (and (= (+ y 1) x$1) (p y))
      (q x$1 x$1))))

