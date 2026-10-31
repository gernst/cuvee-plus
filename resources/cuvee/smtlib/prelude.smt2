; the prelude of SMT-LIB, which is parsed into the initial state and injected at the beginning of the commands,
; where each declaration names the languages that it is part of by their file extensions, :smt2, :dfy, :bpl, :c,
; and the output in one of these languages drops it (see cuvee.pipe.Printer.filter);
; the sorts and functions predefined by SMT-LIB (core, integers, reals, arrays, sequences),
; formal parameters are implicitly named x$0, x$1, ... and type parameters a$0, a$1, ... as in cuvee.core.Fun

(declare-sort Bool 0 :smt2 :dfy :bpl :c)
(declare-sort Int 0 :smt2 :dfy :bpl :c)
(declare-sort Real 0 :smt2 :dfy :bpl)
(declare-sort String 0 :smt2 :dfy)
(declare-sort Array 2 :smt2 :dfy :bpl :c)
(declare-sort Seq 1 :smt2 :dfy :bpl)
; finite sets and multisets as in cvc5
(declare-sort Set 1 :smt2 :dfy)
(declare-sort Bag 1 :smt2 :dfy)

(declare-const true Bool :smt2 :dfy :bpl :c)
(declare-const false Bool :smt2 :dfy :bpl :c)

(declare-fun = (par (a$0) (a$0 a$0) Bool :smt2 :dfy :bpl :c))
(declare-fun ite (par (a$0) (Bool a$0 a$0) a$0 :smt2 :dfy :bpl :c))

(declare-fun select (par (a$0 a$1) ((Array a$0 a$1) a$0) a$1 :smt2 :dfy :bpl :c))
(declare-fun store (par (a$0 a$1) ((Array a$0 a$1) a$0 a$1) (Array a$0 a$1) :smt2 :dfy :bpl :c))

; constant arrays are written ((as const (Array a$0 a$1)) v)
(declare-fun const (par (a$0 a$1) (a$1) (Array a$0 a$1) :smt2 :dfy :bpl :c))

; sequences as in cvc5 (see cuvee.core.Fun.seq)
(declare-fun seq.empty (par (a$0) () (Seq a$0) :smt2 :dfy))
(declare-fun seq.unit (par (a$0) (a$0) (Seq a$0) :smt2 :dfy))
(declare-fun seq.++ (par (a$0) ((Seq a$0) (Seq a$0)) (Seq a$0) :smt2 :dfy))
(declare-fun seq.len (par (a$0) ((Seq a$0)) Int :smt2 :dfy))
(declare-fun seq.nth (par (a$0) ((Seq a$0) Int) a$0 :smt2 :dfy))
(declare-fun seq.update (par (a$0) ((Seq a$0) Int (Seq a$0)) (Seq a$0) :smt2 :dfy))
(declare-fun seq.extract (par (a$0) ((Seq a$0) Int Int) (Seq a$0) :smt2 :dfy))
(declare-fun seq.contains (par (a$0) ((Seq a$0) (Seq a$0)) Bool :smt2 :dfy))
(declare-fun seq.prefixof (par (a$0) ((Seq a$0) (Seq a$0)) Bool :smt2 :dfy))
; not part of cvc5, the implementations of s[i := v], x in s, and s < t (see cuvee.core.Overload), and the extension
; by one element, of which displays are built (the solvers receive (seq.++ s (seq.unit x)), see cuvee.smtlib.Solver)
(declare-fun seq.store (par (a$0) ((Seq a$0) Int a$0) (Seq a$0) :smt2 :dfy))
(declare-fun seq.snoc (par (a$0) ((Seq a$0) a$0) (Seq a$0) :smt2 :dfy))
; not part of cvc5, the slice s[i..j] (the solvers receive (seq.extract s i (- j i)), see cuvee.smtlib.Solver)
(declare-fun seq.slice (par (a$0) ((Seq a$0) Int Int) (Seq a$0) :smt2 :dfy))
(declare-fun seq.member (par (a$0) (a$0 (Seq a$0)) Bool :smt2 :dfy))
(declare-fun seq.proper_prefixof (par (a$0) ((Seq a$0) (Seq a$0)) Bool :smt2 :dfy))

; finite sets as in cvc5 (see cuvee.core.Fun.set)
(declare-fun set.empty (par (a$0) () (Set a$0) :smt2 :dfy))
(declare-fun set.singleton (par (a$0) (a$0) (Set a$0) :smt2 :dfy))
(declare-fun set.union (par (a$0) ((Set a$0) (Set a$0)) (Set a$0) :smt2 :dfy))
(declare-fun set.inter (par (a$0) ((Set a$0) (Set a$0)) (Set a$0) :smt2 :dfy))
(declare-fun set.minus (par (a$0) ((Set a$0) (Set a$0)) (Set a$0) :smt2 :dfy))
(declare-fun set.member (par (a$0) (a$0 (Set a$0)) Bool :smt2 :dfy))
(declare-fun set.subset (par (a$0) ((Set a$0) (Set a$0)) Bool :smt2 :dfy))
(declare-fun set.card (par (a$0) ((Set a$0)) Int :smt2 :dfy))
; not part of cvc5, the implementation of s[x := b], which contains x exactly if b
(declare-fun set.update (par (a$0) ((Set a$0) a$0 Bool) (Set a$0) :smt2 :dfy))
; not part of cvc5, the implementation of s < t
(declare-fun set.proper_subset (par (a$0) ((Set a$0) (Set a$0)) Bool :smt2 :dfy))

; finite multisets as in cvc5 (see cuvee.core.Fun.bag)
(declare-fun bag.empty (par (a$0) () (Bag a$0) :smt2 :dfy))
(declare-fun bag (par (a$0) (a$0 Int) (Bag a$0) :smt2 :dfy))
(declare-fun bag.union_disjoint (par (a$0) ((Bag a$0) (Bag a$0)) (Bag a$0) :smt2 :dfy))
(declare-fun bag.inter_min (par (a$0) ((Bag a$0) (Bag a$0)) (Bag a$0) :smt2 :dfy))
(declare-fun bag.difference_subtract (par (a$0) ((Bag a$0) (Bag a$0)) (Bag a$0) :smt2 :dfy))
(declare-fun bag.count (par (a$0) (a$0 (Bag a$0)) Int :smt2 :dfy))
(declare-fun bag.subbag (par (a$0) ((Bag a$0) (Bag a$0)) Bool :smt2 :dfy))
(declare-fun bag.card (par (a$0) ((Bag a$0)) Int :smt2 :dfy))
(declare-fun bag.member (par (a$0) (a$0 (Bag a$0)) Bool :smt2 :dfy))
; not part of cvc5, the implementations of s[x], s[x := n], and s < t, and the insertion of one occurrence, of which
; displays are built (the solvers receive (bag.union_disjoint s (bag x 1)), see cuvee.smtlib.Solver)
(declare-fun bag.select (par (a$0) ((Bag a$0) a$0) Int :smt2 :dfy))
(declare-fun bag.store (par (a$0) ((Bag a$0) a$0 Int) (Bag a$0) :smt2 :dfy))
(declare-fun bag.insert (par (a$0) ((Bag a$0) a$0) (Bag a$0) :smt2 :dfy))
(declare-fun bag.proper_subbag (par (a$0) ((Bag a$0) (Bag a$0)) Bool :smt2 :dfy))

; finite maps (see cuvee.core.Fun.map), which the solvers are not expected to support
(declare-sort Map 2 :smt2 :dfy)
(declare-fun map.empty (par (a$0 a$1) () (Map a$0 a$1) :smt2 :dfy))
(declare-fun map.singleton (par (a$0 a$1) (a$0 a$1) (Map a$0 a$1) :smt2 :dfy))
(declare-fun map.card (par (a$0 a$1) ((Map a$0 a$1)) Int :smt2 :dfy))
(declare-fun map.member (par (a$0 a$1) (a$0 (Map a$0 a$1)) Bool :smt2 :dfy))
(declare-fun map.keys (par (a$0 a$1) ((Map a$0 a$1)) (Set a$0) :smt2 :dfy))
(declare-fun map.values (par (a$0 a$1) ((Map a$0 a$1)) (Set a$1) :smt2 :dfy))
(declare-fun map.subset (par (a$0 a$1) ((Map a$0 a$1) (Map a$0 a$1)) Bool :smt2 :dfy))
(declare-fun map.get (par (a$0 a$1) ((Map a$0 a$1) a$0) a$1 :smt2 :dfy))
(declare-fun map.update (par (a$0 a$1) ((Map a$0 a$1) (Map a$0 a$1)) (Map a$0 a$1) :smt2 :dfy))
(declare-fun map.minus (par (a$0 a$1) ((Map a$0 a$1) (Set a$0)) (Map a$0 a$1) :smt2 :dfy))
(declare-fun map.store (par (a$0 a$1) ((Map a$0 a$1) a$0 a$1) (Map a$0 a$1) :smt2 :dfy))

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
(declare-fun / (Real Real) Real :smt2 :dfy :bpl)

; the function types (-> A$1 ... A$n R) and their applications (@ f x$1 ... x$n) of SMT-LIB 2.7, of 1 to 10 arguments,
; as the sorts arrow$n, whose last argument is the result, and the functions apply$n (see cuvee.core.Arrow and cuvee.core.Apply),
; which are higher-order (:ho), whose declarations are not passed to solvers
(declare-sort arrow$1 2 :smt2 :dfy :ho)
(declare-sort arrow$2 3 :smt2 :dfy :ho)
(declare-sort arrow$3 4 :smt2 :dfy :ho)
(declare-sort arrow$4 5 :smt2 :dfy :ho)
(declare-sort arrow$5 6 :smt2 :dfy :ho)
(declare-sort arrow$6 7 :smt2 :dfy :ho)
(declare-sort arrow$7 8 :smt2 :dfy :ho)
(declare-sort arrow$8 9 :smt2 :dfy :ho)
(declare-sort arrow$9 10 :smt2 :dfy :ho)
(declare-sort arrow$10 11 :smt2 :dfy :ho)
(declare-fun apply$1 (par (a$0 a$1) ((arrow$1 a$0 a$1) a$0) a$1 :smt2 :dfy :ho))
(declare-fun apply$2 (par (a$0 a$1 a$2) ((arrow$2 a$0 a$1 a$2) a$0 a$1) a$2 :smt2 :dfy :ho))
(declare-fun apply$3 (par (a$0 a$1 a$2 a$3) ((arrow$3 a$0 a$1 a$2 a$3) a$0 a$1 a$2) a$3 :smt2 :dfy :ho))
(declare-fun apply$4 (par (a$0 a$1 a$2 a$3 a$4) ((arrow$4 a$0 a$1 a$2 a$3 a$4) a$0 a$1 a$2 a$3) a$4 :smt2 :dfy :ho))
(declare-fun apply$5 (par (a$0 a$1 a$2 a$3 a$4 a$5) ((arrow$5 a$0 a$1 a$2 a$3 a$4 a$5) a$0 a$1 a$2 a$3 a$4) a$5 :smt2 :dfy :ho))
(declare-fun apply$6 (par (a$0 a$1 a$2 a$3 a$4 a$5 a$6) ((arrow$6 a$0 a$1 a$2 a$3 a$4 a$5 a$6) a$0 a$1 a$2 a$3 a$4 a$5) a$6 :smt2 :dfy :ho))
(declare-fun apply$7 (par (a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7) ((arrow$7 a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7) a$0 a$1 a$2 a$3 a$4 a$5 a$6) a$7 :smt2 :dfy :ho))
(declare-fun apply$8 (par (a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8) ((arrow$8 a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8) a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7) a$8 :smt2 :dfy :ho))
(declare-fun apply$9 (par (a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9) ((arrow$9 a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9) a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8) a$9 :smt2 :dfy :ho))
(declare-fun apply$10 (par (a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10) ((arrow$10 a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10) a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9) a$10 :smt2 :dfy :ho))
