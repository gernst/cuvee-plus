; ./Cuvee.sh -print bpl examples/smtlib/printing/boogie_unsupported.smt2
; other attributes of loops are not supported in Boogie
(define-proc m ((x Int)) ()
  (while true (block (locals)) :other x))
