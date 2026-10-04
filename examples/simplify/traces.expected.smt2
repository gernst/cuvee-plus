; the combinators of trace equation systems: guards and results are simplified, cases with guard false are dropped,
; results are simplified under their guard, and all is true if its body is
(declare-fun J () (Seq Int))

(declare-fun n () Int)

(declare-fun f (Int) Int)

(assert
  (=
    (trace
      (s 0)
      ((j J))
      (cases ((< j n) (+ j s)) ((not (< j n)) s)))
    (trace (s 0) ((j J)) s)))

(assert
  (= (map ((j J)) j) J))

