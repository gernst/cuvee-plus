// the prelude of C, written in Boogie, which the C frontend parses into the initial state
// and injects at the beginning of the commands (see cuvee.c.Source),
// where each declaration names the languages that it is part of by their file extensions, {:c}, {:bpl}, {:dfy}, {:smt2},
// and the output in one of these languages drops it (see cuvee.pipe.Printer.filter)

// the core theory of SMT-LIB with integers and arrays, as in the prelude of Boogie,
// the type parameters are named a₀, a₁, ... and the formal parameters x₀, x₁, ...,
// such that the declarations coincide with the built-in functions (see cuvee.core.Fun)
type {:c} {:bpl} {:dfy} {:smt2} bool;
type {:c} {:bpl} {:dfy} {:smt2} int;
type {:c} {:bpl} {:dfy} {:smt2} array<a₀, a₁>;

const {:c} {:bpl} {:dfy} {:smt2} true: bool;
const {:c} {:bpl} {:dfy} {:smt2} false: bool;

function {:c} {:bpl} {:dfy} {:smt2} == <a₀>(x₀: a₀, x₁: a₀): bool;
function {:c} {:bpl} {:dfy} {:smt2} ite<a₀>(x₀: bool, x₁: a₀, x₂: a₀): a₀;

function {:c} {:bpl} {:dfy} {:smt2} select<a₀, a₁>(x₀: [a₀]a₁, x₁: a₀): a₁;
function {:c} {:bpl} {:dfy} {:smt2} store<a₀, a₁>(x₀: [a₀]a₁, x₁: a₀, x₂: a₁): [a₀]a₁;
// constant arrays, e.g. the initial values of arrays
function {:c} {:bpl} {:dfy} {:smt2} const<a₀, a₁>(x₀: a₁): [a₀]a₁;

function {:c} {:bpl} {:dfy} {:smt2} !(x₀: bool): bool;
function {:c} {:bpl} {:dfy} {:smt2} &&(x₀: bool, x₁: bool): bool;
function {:c} {:bpl} {:dfy} {:smt2} ||(x₀: bool, x₁: bool): bool;
function {:c} {:bpl} {:dfy} {:smt2} ==>(x₀: bool, x₁: bool): bool;
function {:c} {:bpl} {:dfy} {:smt2} <==>(x₀: bool, x₁: bool): bool;

// arithmetic and comparison on int only, which C applies to integers (see cuvee.core.Fun.int)
function {:c} {:bpl} {:dfy} {:smt2} -(x₀: int): int;
function {:c} {:bpl} {:dfy} {:smt2} +(x₀: int, x₁: int): int;
function {:c} {:bpl} {:dfy} {:smt2} -(x₀: int, x₁: int): int;
function {:c} {:bpl} {:dfy} {:smt2} *(x₀: int, x₁: int): int;

function {:c} {:bpl} {:dfy} {:smt2} <(x₀: int, x₁: int): bool;
function {:c} {:bpl} {:dfy} {:smt2} <=(x₀: int, x₁: int): bool;
function {:c} {:bpl} {:dfy} {:smt2} >(x₀: int, x₁: int): bool;
function {:c} {:bpl} {:dfy} {:smt2} >=(x₀: int, x₁: int): bool;

function {:c} {:bpl} {:dfy} {:smt2} div(x₀: int, x₁: int): int;
function {:c} {:bpl} {:dfy} {:smt2} mod(x₀: int, x₁: int): int;

// the background theory of C

// pointers to values of type a: the null pointer, and the others by their address
data {:c} Ptr<a> = null | ptr(addr: int);

// the pointee of untyped pointers, void * as Ptr<Void>, whose values carry no information
data {:c} Void = void;

// integers as truth values, e.g. the conditions of if and while, which the simplifier unfolds (rw)
function {:c} {:rw} truth(x: int): bool { x != 0 }

// truth values as integers, e.g. in arithmetic, which the simplifier unfolds (rw)
function {:c} {:rw} number(b: bool): int { if b then 1 else 0 }

// division and remainder of C, which truncate towards zero, e.g. -7 / 2 == -3 and -7 % 2 == -1,
// unlike div and mod of SMT-LIB, whose remainder is nonnegative, with which they coincide for nonnegative dividends,
// which the simplifier unfolds (rw); also in the prelude of Dafny (resources/cuvee/dafny/prelude.dfy)
function {:c} {:dfy} {:rw} quot(a: int, b: int): int { if 0 <= a then a div b else -((-a) div b) }

function {:c} {:dfy} {:rw} rem(a: int, b: int): int { if 0 <= a then a mod b else -((-a) mod b) }

// the arithmetic of unsigned integers of 1, 2, 4, and 8 bytes, modulo the size of their range, e.g. UINT_MAX + 1 == 0
// and 0 - 1 == UINT_MAX, which the C frontend applies to the results of +, -, *, and shifts left in an unsigned type,
// and to conversions of values to an unsigned type (see cuvee.c.Parser.overflow, not with -unbounded), and which the
// simplifier unfolds (rw); unsigned long is unsigned int or unsigned long long by the data model, and the overflow of
// signed integers is undefined in C, hence not modelled
function {:c} {:rw} uchar(x: int): int { x mod 256 }

function {:c} {:rw} ushort(x: int): int { x mod 65536 }

function {:c} {:rw} uint(x: int): int { x mod 4294967296 }

function {:c} {:rw} ulonglong(x: int): int { x mod 18446744073709551616 }

// the bit operations on integers, &, |, ^, ~, and the shifts << and >> by values that are not constants, which are
// declared only, since the integers are unbounded (shifts by constants are multiplications and divisions), and
// :abstract, such that -verify takes a refutation of a goal that applies them for no counterexample (see pipe.Verify)
function {:c} {:abstract} bitand(a: int, b: int): int;
function {:c} {:abstract} bitor(a: int, b: int): int;
function {:c} {:abstract} bitxor(a: int, b: int): int;
function {:c} {:abstract} bitnot(a: int): int;
function {:c} {:abstract} shl(a: int, b: int): int;
function {:c} {:abstract} shr(a: int, b: int): int;

// &, |, ^ on 0 and 1, the truth values as integers, e.g. (y < 100 ? 1 : 0) & (x < 100 ? 1 : 0), which the C frontend
// writes as and, or, xor only on operands of the type of truth values (see cuvee.c.Parser.logical); rules of the
// simplifier (rw), which are not passed to the solvers ({:smt2}, assumed known), since Horn solvers reject
// uninterpreted functions in their clauses; the operations stay uninterpreted on other integers
axiom {:c} {:smt2} {:rw} (forall c: bool, d: bool :: bitand(if c then 1 else 0, if d then 1 else 0) == (if c && d then 1 else 0));
axiom {:c} {:smt2} {:rw} (forall c: bool, d: bool :: bitor(if c then 1 else 0, if d then 1 else 0) == (if c || d then 1 else 0));
axiom {:c} {:smt2} {:rw} (forall c: bool, d: bool :: bitxor(if c then 1 else 0, if d then 1 else 0) == (if c != d then 1 else 0));

// the constants 0 and 1, e.g. after case splits
axiom {:c} {:smt2} {:rw} (forall x: int :: bitand(0, x) == 0);
axiom {:c} {:smt2} {:rw} (forall x: int :: bitand(x, 0) == 0);
axiom {:c} {:smt2} {:rw} bitand(1, 1) == 1;
axiom {:c} {:smt2} {:rw} (forall x: int :: bitor(0, x) == x);
axiom {:c} {:smt2} {:rw} (forall x: int :: bitor(x, 0) == x);
axiom {:c} {:smt2} {:rw} bitor(1, 1) == 1;
axiom {:c} {:smt2} {:rw} (forall x: int :: bitxor(0, x) == x);
axiom {:c} {:smt2} {:rw} (forall x: int :: bitxor(x, 0) == x);
axiom {:c} {:smt2} {:rw} bitxor(1, 1) == 0;
