; ./Cuvee.sh -print bpl examples/smtlib/printing/accumulators.smt2
; traces of several accumulators in SMT-LIB: the accumulators bound like the dependencies, one result each, and the
; components ((_ current i) S) and histories ((_ butlast i) S), with the declarations of teq.dfy that they need,
; and the tuple of the state, which SMT-LIB input does not declare
(declare-datatype tuple$2 (par (a$0 a$1) ((tuple$2 (|tuple₂_0| a$0) (|tuple₂_1| a$1)))))

(declare-sort Trace 1)

(declare-sort List 1)

(declare-fun butlast (par (a$0) ((Trace a$0)) (List a$0)))

(declare-fun current (par (a$0) ((Trace a$0)) a$0))

(define-fun swap ((K (List Int)) (S (Trace (tuple$2 Int Bool)))) Bool
  (=>
    (= S (trace ((x 0) (b true)) ((k K)) (eps (b (+ x k)) ((not b) x)) (not b)))
    (and
      (<= 0 ((_ current 0) S))
      (invs ((k K) (y ((_ butlast 0) S)) (c ((_ butlast 1) S))) (or c (<= 0 y))))))
