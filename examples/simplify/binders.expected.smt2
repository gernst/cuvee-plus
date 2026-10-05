(declare-fun p (Int) Bool)

(assert
  (forall ((y Int)) (p y)))

(assert
  (forall
    ((y Int) (x$2 Int))
    (=> (= x$2 1) (< x$2 y))))

(assert
  (forall
    ((y Int) (x$3 Int))
    (=> (= x$3 y) (p x$3))))

(assert
  (forall ((x$4 Int)) (p x$4)))

(assert
  (forall
    ((x Int))
    (=>
      (p x)
      (exists ((z Int)) (and (p z) (< x z))))))

