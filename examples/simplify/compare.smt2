; ./Cuvee.sh -simplify examples/simplify/compare.smt2
; negated comparisons are the other comparison with the arguments swapped,
; which the context relates to the original comparison
(declare-const x Int)
(declare-const y Int)
(declare-const a Real)
(declare-const b Real)
(assert (not (< x y)))
(assert (not (<= x y)))
(assert (not (< a b)))
(assert (not (<= a b)))
(assert (=> (<= y x) (< x y)))
(assert (=> (< x y) (or (<= y x) (< x y))))
