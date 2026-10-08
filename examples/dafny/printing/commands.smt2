; ./Cuvee.sh -print dfy examples/dafny/printing/commands.smt2
; top-level commands are printed without semicolon
(declare-const c Int)
(push 1)
(check-sat)
(get-model)
(pop 1)
