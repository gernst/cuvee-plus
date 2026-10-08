; ./Cuvee.sh -flat examples/transform/flat_equations.smt2
; equations x == t of bound variables in the antecedent are inlined, also t == x,
; those of free variables and those where x occurs in t are kept, as are formulas that are not clauses
(declare-fun p (Int Int) Bool)
(declare-const g Int)
(declare-const x Int)
(declare-const y Int)
(assert (forall ((x Int) (y Int)) (=> (and (= x (+ y 1)) (p x y)) (p y x))))
(assert (forall ((x Int) (y Int)) (=> (and (p x y) (= y x)) (p y 0))))
(assert (forall ((z Int)) (=> (and (= g (+ z 1)) (= z (+ z 1)) (p z z)) (p g z))))
(assert (=> (= x y) (p x y)))
