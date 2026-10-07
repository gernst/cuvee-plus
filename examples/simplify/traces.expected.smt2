; the combinators of trace equation systems: guards and results are simplified, cases with guard false are dropped,
; results are simplified under their guard, and all is true if its body is;
; dependencies whose bound variables are unused are dropped, except counters and the first one if none remains,
; and equal dependencies are collapsed
(declare-fun J () (Seq Int))

(declare-fun n () Int)

(declare-fun f (Int) Int)

(declare-fun K () (Seq Int))

(assert
  (=
    (trace
      (s 0)
      ((j J))
      (eps ((< j n) (+ j s)) ((<= n j) s)))
    (trace (s 0) ((j J)) s)))

(assert
  (= (map ((j J)) j) J))

(assert
  (all ((j J)) (< (* 2 j) n)))

(assert
  (all ((k K)) (< 0 n)))

