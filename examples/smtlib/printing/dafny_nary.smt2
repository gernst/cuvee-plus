; ./Cuvee.sh -print dfy examples/smtlib/printing/dafny_nary.smt2
; n-ary sums are printed as nested ones, n-ary equations as applications, negative literals without parentheses
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y 0) 0))
(assert (= x y 0))
(assert (= (- x (* y (- 1))) 0))
