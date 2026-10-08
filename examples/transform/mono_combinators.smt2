; ./Cuvee.sh -monomorph examples/transform/mono_combinators.smt2
; polymorphic functions are replaced by their instances also inside the combinators of trace equation systems
(declare-sort Lst 1)
(declare-fun single (par (a) (a) (Lst a)))
(declare-const J (Seq Int))
(assert (= (map ((j J)) (single j)) (map ((j J)) (single (+ j 0)))))
