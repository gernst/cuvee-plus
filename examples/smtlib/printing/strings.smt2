; ./Cuvee.sh examples/smtlib/printing/strings.smt2
; a doubled "" inside a string stands for " (SMT-LIB 2.6)
(assert (= "a""b" ""))
