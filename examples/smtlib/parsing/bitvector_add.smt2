; ./Cuvee.sh -print null examples/smtlib/parsing/bitvector_add.smt2
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #b1) x))
