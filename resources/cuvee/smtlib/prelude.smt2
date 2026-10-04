; sorts and functions predefined by SMT-LIB (core, integers, reals, arrays),
; formal parameters are implicitly named x$0, x$1, ... as in cuvee.core.Fun

(declare-sort Bool 0)
(declare-sort Int 0)
(declare-sort Real 0)
(declare-sort String 0)
(declare-sort Array 2)
(declare-sort Seq 1)

(declare-const true Bool)
(declare-const false Bool)

(declare-fun = (par (a) (a a) Bool))
(declare-fun ite (par (a) (Bool a a) a))

(declare-fun select (par (a b) ((Array a b) a) b))
(declare-fun store (par (a b) ((Array a b) a b) (Array a b)))

; constant arrays are written ((as const (Array a b)) v)
(declare-fun const (par (a b) (b) (Array a b)))

; sequences as in cvc5 (see cuvee.core.Fun.seq)
(declare-fun seq.empty (par (a) () (Seq a)))
(declare-fun seq.unit (par (a) (a) (Seq a)))
(declare-fun seq.++ (par (a) ((Seq a) (Seq a)) (Seq a)))
(declare-fun seq.len (par (a) ((Seq a)) Int))
(declare-fun seq.nth (par (a) ((Seq a) Int) a))
(declare-fun seq.update (par (a) ((Seq a) Int (Seq a)) (Seq a)))
(declare-fun seq.extract (par (a) ((Seq a) Int Int) (Seq a)))
(declare-fun seq.contains (par (a) ((Seq a) (Seq a)) Bool))
(declare-fun seq.prefixof (par (a) ((Seq a) (Seq a)) Bool))

(declare-fun not (Bool) Bool)
(declare-fun => (Bool Bool) Bool)

; not part of SMT-LIB, kept explicit for readability and printed as =
(declare-fun <=> (Bool Bool) Bool)

(declare-fun and (Bool Bool) Bool)
(declare-fun or (Bool Bool) Bool)

; arithmetic and comparison on Int and Real are generic,
; each application is resolved after type checking (see cuvee.core.Overload)
(declare-fun - (par (a) (a) a))
(declare-fun + (par (a) (a a) a))
(declare-fun - (par (a) (a a) a))
(declare-fun * (par (a) (a a) a))

(declare-fun < (par (a) (a a) Bool))
(declare-fun <= (par (a) (a a) Bool))
(declare-fun > (par (a) (a a) Bool))
(declare-fun >= (par (a) (a a) Bool))

(declare-fun div (Int Int) Int)
(declare-fun mod (Int Int) Int)
(declare-fun / (Real Real) Real)
