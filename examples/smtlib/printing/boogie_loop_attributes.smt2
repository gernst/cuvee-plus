; ./Cuvee.sh -print bpl examples/smtlib/printing/boogie_loop_attributes.smt2
; other attributes of loops follow the keyword while in Boogie, as in Dafny, which Boogie does not have; the loop is in
; a sequence, since an annotation of the whole body is that of the procedure
(define-proc m ((x Int)) () ()
  (sequence (! (while true (sequence)) :other x)))
