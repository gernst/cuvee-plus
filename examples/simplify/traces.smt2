; ./Cuvee.sh -simplify examples/simplify/traces.smt2
; the combinators of trace equation systems: guards and results are simplified, cases with guard false are dropped,
; results are simplified under their guard, and all is true if its body is;
; dependencies whose bound variables are unused are dropped, except counters and the first one if none remains,
; and equal dependencies are collapsed
(declare-const J (Seq Int))
(declare-const n Int)
(declare-fun f (Int) Int)
(declare-const K (Seq Int))
(assert (= (trace (s 0) ((j J)) (eps ((< j n) (+ s (* 2 j) (- j))) ((and (< j n) (not (< j n))) s) ((not (< j n)) (ite (< j n) 1 s)))) (trace (s 0) ((j J)) (+ s 0))))
(assert (all ((j J)) (=> (< j n) (or (< j n) (= (f j) 0)))))
(assert (= (map ((j J)) (+ j 1 (- 1))) J))
(assert (all ((k K) (j J) (i J)) (< (+ i j) n)))
(assert (all ((k K) (j J)) (< 0 n)))
