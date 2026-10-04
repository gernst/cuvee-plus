; polymorphic predicates over generic records, where Box has a parameter that none of its fields refers to
(declare-datatype Pair (par (a b) ((pair (fst a) (snd b)))))
(declare-datatype Box (par (a) ((box (size Int)))))
(declare-fun q (par (a) ((Pair a (Box a))) Bool))
(assert (par (a) (forall ((x (Pair a (Box a))) (y a))
  (=> (and (= (size (snd x)) 0) (= x (pair y (box 1)))) (q x)))))
