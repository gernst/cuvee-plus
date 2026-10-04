; the built-in sorts and functions, which SMT-LIB knows, or which are eliminated before the output,
; they are parsed into the initial state and not passed on (unlike prelude.smt2)
; sorts and functions predefined by SMT-LIB (core, integers, reals, arrays, sequences),
; formal parameters are implicitly named x$0, x$1, ... and type parameters a$0, a$1, ... as in cuvee.core.Fun

(declare-sort Bool 0)
(declare-sort Int 0)
(declare-sort Real 0)
(declare-sort String 0)
(declare-sort Array 2)
(declare-sort Seq 1)
; not SMT-LIB, the traces of trace equation systems (see cuvee.core.Sort.trace)
(declare-sort Trace 1)

(declare-const true Bool)
(declare-const false Bool)

(declare-fun = (par (a$0) (a$0 a$0) Bool))
(declare-fun ite (par (a$0) (Bool a$0 a$0) a$0))

(declare-fun select (par (a$0 a$1) ((Array a$0 a$1) a$0) a$1))
(declare-fun store (par (a$0 a$1) ((Array a$0 a$1) a$0 a$1) (Array a$0 a$1)))

; constant arrays are written ((as const (Array a$0 a$1)) v)
(declare-fun const (par (a$0 a$1) (a$1) (Array a$0 a$1)))

; sequences as in cvc5 (see cuvee.core.Fun.seq)
(declare-fun seq.empty (par (a$0) () (Seq a$0)))
(declare-fun seq.unit (par (a$0) (a$0) (Seq a$0)))
(declare-fun seq.++ (par (a$0) ((Seq a$0) (Seq a$0)) (Seq a$0)))
(declare-fun seq.len (par (a$0) ((Seq a$0)) Int))
(declare-fun seq.nth (par (a$0) ((Seq a$0) Int) a$0))
(declare-fun seq.update (par (a$0) ((Seq a$0) Int (Seq a$0)) (Seq a$0)))
(declare-fun seq.extract (par (a$0) ((Seq a$0) Int Int) (Seq a$0)))
(declare-fun seq.contains (par (a$0) ((Seq a$0) (Seq a$0)) Bool))
(declare-fun seq.prefixof (par (a$0) ((Seq a$0) (Seq a$0)) Bool))

; not SMT-LIB, all but the last element of a trace (see cuvee.core.Fun.trace)
(declare-fun butlast (par (a$0) ((Trace a$0)) (Seq a$0)))

(declare-fun not (Bool) Bool)
(declare-fun => (Bool Bool) Bool)

; not part of SMT-LIB, kept explicit for readability and printed as =
(declare-fun <=> (Bool Bool) Bool)

(declare-fun and (Bool Bool) Bool)
(declare-fun or (Bool Bool) Bool)

; arithmetic and comparison on Int and Real are generic,
; each application is resolved after type checking (see cuvee.core.Overload)
(declare-fun - (par (a$0) (a$0) a$0))
(declare-fun + (par (a$0) (a$0 a$0) a$0))
(declare-fun - (par (a$0) (a$0 a$0) a$0))
(declare-fun * (par (a$0) (a$0 a$0) a$0))

(declare-fun < (par (a$0) (a$0 a$0) Bool))
(declare-fun <= (par (a$0) (a$0 a$0) Bool))
(declare-fun > (par (a$0) (a$0 a$0) Bool))
(declare-fun >= (par (a$0) (a$0 a$0) Bool))

(declare-fun div (Int Int) Int)
(declare-fun mod (Int Int) Int)
(declare-fun / (Real Real) Real)
