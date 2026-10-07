// the background theory of C, written in Boogie, which the C frontend parses after the prelude of SMT-LIB
// and injects at the beginning of the commands (see cuvee.c.Source),
// where each declaration names the languages that it is part of by their file extensions, here {:c},
// and the output in one of these languages drops it (see cuvee.pipe.Sink.filter)

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
