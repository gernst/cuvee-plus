; ./Cuvee.sh -prove examples/smtlib/prove/distinct.smt2
; distinct is n-ary, two arguments are simplified to a negated equation
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (distinct x y))
(assert (distinct x y z))
(assert (distinct x y x))
(assert (distinct 1 2 3))
(assert (distinct 1 (+ 0 1)))
(assert (distinct true false))
(assert (=> (= x y) (distinct x y z)))
(assert (forall ((a Int) (b Int)) (=> (= a b) (distinct a b z))))
