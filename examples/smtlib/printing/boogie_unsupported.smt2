; ./Cuvee.sh -print bpl examples/smtlib/printing/boogie_unsupported.smt2
; other attributes of loops are not supported in Boogie; the loop is in a sequence, since an annotation of the
; whole body is that of the procedure
(define-proc m ((x Int)) () ()
  (sequence (! (while true (sequence)) :other x)))
