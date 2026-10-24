; ./Cuvee.sh -prove examples/smtlib/prove/rewrite_products.smt2
; products are matched modulo associativity, commutativity, and the neutral element 1 if they do not match position by
; position (Rewrite.matchesFactors): the pattern a * x * x matches y * y with a = 1, whose normal form has no factor 1,
; and 3 * y * y as it is; a factor 1 only for a product, so the single factor z is not matched with a = 1
(declare-fun g (Int) Int)
(declare-const y Int)
(declare-const z Int)
(assert (! (forall ((a Int) (x Int)) (= (g (* a x x)) a)) :rw))
(assert (! (= (g (* y y)) 1) :lemma))
(assert (! (= (g (* 3 y y)) 3) :lemma))
(assert (! (= (g z) 0) :lemma))
