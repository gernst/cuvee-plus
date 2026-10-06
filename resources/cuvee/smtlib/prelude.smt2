; the prelude of SMT-LIB, which is parsed into the initial state and injected at the beginning of the commands,
; where each declaration names the languages that it is part of by their file extensions, :smt2, :dfy, :bpl, :c,
; and the output in one of these languages drops it (see cuvee.transform.Language);
; the sorts and functions predefined by SMT-LIB (core, integers, reals, arrays, sequences),
; formal parameters are implicitly named x$0, x$1, ... and type parameters a$0, a$1, ... as in cuvee.core.Fun

(declare-sort Bool 0 :smt2 :dfy :bpl :c)
(declare-sort Int 0 :smt2 :dfy :bpl :c)
(declare-sort Real 0 :smt2 :dfy :bpl :c)
(declare-sort String 0 :smt2 :dfy :c)
(declare-sort Array 2 :smt2 :dfy :bpl :c)
(declare-sort Seq 1 :smt2 :dfy :bpl :c)
; finite sets and multisets as in cvc5
(declare-sort Set 1 :smt2 :dfy :c)
(declare-sort Bag 1 :smt2 :dfy :c)

(declare-const true Bool :smt2 :dfy :bpl :c)
(declare-const false Bool :smt2 :dfy :bpl :c)

(declare-fun = (par (a$0) (a$0 a$0) Bool :smt2 :dfy :bpl :c))
(declare-fun ite (par (a$0) (Bool a$0 a$0) a$0 :smt2 :dfy :bpl :c))

(declare-fun select (par (a$0 a$1) ((Array a$0 a$1) a$0) a$1 :smt2 :dfy :bpl :c))
(declare-fun store (par (a$0 a$1) ((Array a$0 a$1) a$0 a$1) (Array a$0 a$1) :smt2 :dfy :bpl :c))

; constant arrays are written ((as const (Array a$0 a$1)) v)
(declare-fun const (par (a$0 a$1) (a$1) (Array a$0 a$1) :smt2 :c))

; sequences as in cvc5 (see cuvee.core.Fun.seq)
(declare-fun seq.empty (par (a$0) () (Seq a$0) :smt2 :dfy :c))
(declare-fun seq.unit (par (a$0) (a$0) (Seq a$0) :smt2 :dfy :c))
(declare-fun seq.++ (par (a$0) ((Seq a$0) (Seq a$0)) (Seq a$0) :smt2 :dfy :c))
(declare-fun seq.len (par (a$0) ((Seq a$0)) Int :smt2 :dfy :c))
(declare-fun seq.nth (par (a$0) ((Seq a$0) Int) a$0 :smt2 :dfy :c))
(declare-fun seq.update (par (a$0) ((Seq a$0) Int (Seq a$0)) (Seq a$0) :smt2 :dfy :c))
(declare-fun seq.extract (par (a$0) ((Seq a$0) Int Int) (Seq a$0) :smt2 :dfy :c))
(declare-fun seq.contains (par (a$0) ((Seq a$0) (Seq a$0)) Bool :smt2 :dfy :c))
(declare-fun seq.prefixof (par (a$0) ((Seq a$0) (Seq a$0)) Bool :smt2 :dfy :c))

; finite sets as in cvc5 (see cuvee.core.Fun.set)
(declare-fun set.empty (par (a$0) () (Set a$0) :smt2 :dfy :c))
(declare-fun set.singleton (par (a$0) (a$0) (Set a$0) :smt2 :dfy :c))
(declare-fun set.union (par (a$0) ((Set a$0) (Set a$0)) (Set a$0) :smt2 :dfy :c))
(declare-fun set.inter (par (a$0) ((Set a$0) (Set a$0)) (Set a$0) :smt2 :dfy :c))
(declare-fun set.minus (par (a$0) ((Set a$0) (Set a$0)) (Set a$0) :smt2 :dfy :c))
(declare-fun set.member (par (a$0) (a$0 (Set a$0)) Bool :smt2 :dfy :c))
(declare-fun set.subset (par (a$0) ((Set a$0) (Set a$0)) Bool :smt2 :dfy :c))
(declare-fun set.card (par (a$0) ((Set a$0)) Int :smt2 :dfy :c))

; finite multisets as in cvc5 (see cuvee.core.Fun.bag)
(declare-fun bag.empty (par (a$0) () (Bag a$0) :smt2 :dfy :c))
(declare-fun bag (par (a$0) (a$0 Int) (Bag a$0) :smt2 :dfy :c))
(declare-fun bag.union_disjoint (par (a$0) ((Bag a$0) (Bag a$0)) (Bag a$0) :smt2 :dfy :c))
(declare-fun bag.inter_min (par (a$0) ((Bag a$0) (Bag a$0)) (Bag a$0) :smt2 :dfy :c))
(declare-fun bag.difference_subtract (par (a$0) ((Bag a$0) (Bag a$0)) (Bag a$0) :smt2 :dfy :c))
(declare-fun bag.count (par (a$0) (a$0 (Bag a$0)) Int :smt2 :dfy :c))
(declare-fun bag.subbag (par (a$0) ((Bag a$0) (Bag a$0)) Bool :smt2 :dfy :c))
(declare-fun bag.card (par (a$0) ((Bag a$0)) Int :smt2 :dfy :c))

; finite maps (see cuvee.core.Fun.map), which the solvers are not expected to support
(declare-sort Map 2 :smt2 :dfy :c)
(declare-fun map.empty (par (a$0 a$1) () (Map a$0 a$1) :smt2 :dfy :c))
(declare-fun map.singleton (par (a$0 a$1) (a$0 a$1) (Map a$0 a$1) :smt2 :dfy :c))
(declare-fun map.card (par (a$0 a$1) ((Map a$0 a$1)) Int :smt2 :dfy :c))
(declare-fun map.member (par (a$0 a$1) (a$0 (Map a$0 a$1)) Bool :smt2 :dfy :c))
(declare-fun map.keys (par (a$0 a$1) ((Map a$0 a$1)) (Set a$0) :smt2 :dfy :c))
(declare-fun map.values (par (a$0 a$1) ((Map a$0 a$1)) (Set a$1) :smt2 :dfy :c))
(declare-fun map.subset (par (a$0 a$1) ((Map a$0 a$1) (Map a$0 a$1)) Bool :smt2 :dfy :c))
(declare-fun map.get (par (a$0 a$1) ((Map a$0 a$1) a$0) a$1 :smt2 :dfy :c))
(declare-fun map.update (par (a$0 a$1) ((Map a$0 a$1) (Map a$0 a$1)) (Map a$0 a$1) :smt2 :dfy :c))
(declare-fun map.minus (par (a$0 a$1) ((Map a$0 a$1) (Set a$0)) (Map a$0 a$1) :smt2 :dfy :c))

(declare-fun not (Bool) Bool :smt2 :dfy :bpl :c)
(declare-fun => (Bool Bool) Bool :smt2 :dfy :bpl :c)

; not part of SMT-LIB, kept explicit for readability and printed as =
(declare-fun <=> (Bool Bool) Bool :smt2 :dfy :bpl :c)

(declare-fun and (Bool Bool) Bool :smt2 :dfy :bpl :c)
(declare-fun or (Bool Bool) Bool :smt2 :dfy :bpl :c)

; arithmetic and comparison on Int and Real are generic,
; each application is resolved after type checking (see cuvee.core.Overload)
(declare-fun - (par (a$0) (a$0) a$0 :smt2 :dfy :bpl :c))
(declare-fun + (par (a$0) (a$0 a$0) a$0 :smt2 :dfy :bpl :c))
(declare-fun - (par (a$0) (a$0 a$0) a$0 :smt2 :dfy :bpl :c))
(declare-fun * (par (a$0) (a$0 a$0) a$0 :smt2 :dfy :bpl :c))

(declare-fun < (par (a$0) (a$0 a$0) Bool :smt2 :dfy :bpl :c))
(declare-fun <= (par (a$0) (a$0 a$0) Bool :smt2 :dfy :bpl :c))
(declare-fun > (par (a$0) (a$0 a$0) Bool :smt2 :dfy :bpl :c))
(declare-fun >= (par (a$0) (a$0 a$0) Bool :smt2 :dfy :bpl :c))

(declare-fun div (Int Int) Int :smt2 :dfy :bpl :c)
(declare-fun mod (Int Int) Int :smt2 :dfy :bpl :c)
(declare-fun / (Real Real) Real :smt2 :dfy :bpl :c)
