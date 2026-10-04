; the combinators of trace equation systems: guards and results are simplified, cases with guard false are dropped,
; results are simplified under their guard, and all is true if its body is
(declare-const J (Seq Int))
(declare-const n Int)
(declare-fun f (Int) Int)
(assert (= (trace (s 0) ((j J)) (cases ((< j n) (+ s (* 2 j) (- j))) ((and (< j n) (not (< j n))) s) ((not (< j n)) (ite (< j n) 1 s)))) (trace (s 0) ((j J)) (+ s 0))))
(assert (all ((j J)) (=> (< j n) (or (< j n) (= (f j) 0)))))
(assert (= (map ((j J)) (+ j 1 (- 1))) J))
