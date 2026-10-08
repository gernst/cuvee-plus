; ./Cuvee.sh -print null examples/smtlib/parsing/bitvector_extract.smt2
(declare-const x (_ BitVec 8))
(assert (= ((_ extract 8 0) x) x))
