; ./Cuvee.sh -print null examples/smtlib/parsing/internal.smt2
; exceptions other than cuvee.Error are reported as internal errors, which stop the run
(push 99999999999999999999999)
(check-sat)
