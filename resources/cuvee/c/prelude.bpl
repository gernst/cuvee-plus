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
function {:c} {:smt2} const<a₀, a₁>(x₀: a₁): [a₀]a₁;

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
// which the simplifier unfolds (rw)
function {:c} {:rw} quotient(a: int, b: int): int { if 0 <= a then a div b else -((-a) div b) }

function {:c} {:rw} remainder(a: int, b: int): int { if 0 <= a then a mod b else -((-a) mod b) }
