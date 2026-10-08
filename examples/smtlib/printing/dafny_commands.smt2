; ./Cuvee.sh -print dfy examples/smtlib/printing/dafny_commands.smt2
; top-level commands are printed without semicolon
(declare-const c Int)
(push 1)
(check-sat)
(get-model)
(pop 1)
