; ./Cuvee.sh examples/smtlib/datatypes.smt2
; generic, recursive, and mutually recursive datatypes

(declare-datatype Color ((red) (green) (blue)))
(declare-datatype Stack (par (a) ((nil) (cons (head a) (tail (Stack a))))))

(declare-datatypes ((Tree 0) (Forest 0))
  (((node (label Int) (children Forest)))
   ((empty) (grow (first Tree) (rest Forest)))))

(declare-const xs (Stack Int))
(assert (= xs (cons 1 (cons 2 nil))))
(assert (= (head (tail xs)) 2))
(assert (distinct red green blue))
(assert (= (label (node 1 empty)) 1))
(check-sat)
(exit)
