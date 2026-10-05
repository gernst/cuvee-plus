(declare-fun p (Int) Bool)

(assert
  (forall
    ((x Int) (y Int))
    (=>
      (= x y)
      (exists
        ((x$1 Int))
        (and (= x$1 y) (p y))))))

(assert
  (forall
    ((x Int) (y Int) (x$2 Int))
    (=>
      (and (= x y) (= x$2 1))
      (< x$2 y))))

(assert
  (forall
    ((x Int) (y Int) (x$3 Int))
    (=>
      (and (= x y) (= x$3 y))
      (p x$3))))

(assert
  (forall ((x$4 Int)) (p x$4)))

(assert
  (forall
    ((x Int))
    (=>
      (p x)
      (exists ((z Int)) (and (p z) (< x z))))))

