; ./Cuvee.sh -print null examples/smtlib/parsing/bitvector_widths.smt2
; the functions are instantiated for the widths of their arguments, compared to literals of the expected width
(declare-const x (_ BitVec 8))
(assert (= (concat x #b1) #b000000000))
(assert (= ((_ extract 3 0) x) #b0000))
(assert (= ((_ repeat 3) x) #x000000))
(assert (= (bvcomp x x) #b1))
