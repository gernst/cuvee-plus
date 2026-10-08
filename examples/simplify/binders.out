(declare-fun p (Int) Bool)

(assert
  (forall ((y Int)) (p y)))

(assert
  (forall ((y Int)) (< 1 y)))

(assert
  (forall ((x$3 Int)) (p x$3)))

(assert
  (forall ((x$4 Int)) (p x$4)))

(assert
  (forall
    ((x Int))
    (=>
      (p x)
      (exists ((z Int)) (and (p z) (< x z))))))

