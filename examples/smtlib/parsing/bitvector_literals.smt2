; ./Cuvee.sh examples/smtlib/parsing/bitvector_literals.smt2
; bitvector literals in hexadecimal, binary, and decimal notation
(assert (= #xff ((_ int2bv 8) 255)))
(assert (= #b101 ((_ int2bv 3) 5)))
(assert (= (_ bv5 16) ((_ int2bv 16) 5)))
