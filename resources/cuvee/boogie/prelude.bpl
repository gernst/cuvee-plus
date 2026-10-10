// the prelude of Boogie, which is parsed into the initial state and injected at the beginning of the commands,
// where each declaration names the languages that it is part of by their file extensions, {:bpl}, {:dfy}, {:smt2}, {:c},
// and the output in one of these languages drops it (see cuvee.pipe.Printer.filter)
// base types
type {:bpl} {:dfy} {:smt2} {:c} bool;
type {:bpl} {:dfy} {:smt2} {:c} int;
type {:bpl} {:dfy} {:smt2} real;

// SMT-LIB array, written [a]b in Boogie
type {:bpl} {:dfy} {:smt2} {:c} array<a₀, a₁>;

// sequences, e.g. the dependencies of the combinators of trace equation systems
type {:bpl} {:dfy} {:smt2} Seq<a₀>;

const {:bpl} {:dfy} {:smt2} {:c} true: bool;
const {:bpl} {:dfy} {:smt2} {:c} false: bool;

// built-in functions (fixity/precedence is built-in),
// the type parameters are named a₀, a₁, ... and the formal parameters x₀, x₁, ...,
// such that the declarations coincide with the built-in functions (see cuvee.core.Fun)
function {:bpl} {:dfy} {:smt2} {:c} == <a₀>(x₀: a₀, x₁: a₀): bool;

function {:bpl} {:dfy} {:smt2} {:c} ite<a₀>(x₀: bool, x₁: a₀, x₂: a₀): a₀;
function {:bpl} {:dfy} {:smt2} {:c} select<a₀, a₁>(x₀: [a₀]a₁, x₁: a₀): a₁;
function {:bpl} {:dfy} {:smt2} {:c} store<a₀, a₁>(x₀: [a₀]a₁, x₁: a₀, x₂: a₁): [a₀]a₁;
// constant arrays, e.g. the initial values of arrays
function {:bpl} {:dfy} {:smt2} {:c} const<a₀, a₁>(x₀: a₁): [a₀]a₁;

function {:bpl} {:dfy} {:smt2} {:c} !(x₀: bool): bool;
function {:bpl} {:dfy} {:smt2} {:c} &&(x₀: bool, x₁: bool): bool;
function {:bpl} {:dfy} {:smt2} {:c} ||(x₀: bool, x₁: bool): bool;
function {:bpl} {:dfy} {:smt2} {:c} ==>(x₀: bool, x₁: bool): bool;
function {:bpl} {:dfy} {:smt2} {:c} <==>(x₀: bool, x₁: bool): bool;

// arithmetic and comparison on int and real are generic,
// each application is resolved after type checking (see cuvee.core.Overload)
function {:bpl} {:dfy} {:smt2} {:c} - <a₀>(x₀: a₀): a₀;
function {:bpl} {:dfy} {:smt2} {:c} + <a₀>(x₀: a₀, x₁: a₀): a₀;
function {:bpl} {:dfy} {:smt2} {:c} - <a₀>(x₀: a₀, x₁: a₀): a₀;
function {:bpl} {:dfy} {:smt2} {:c} * <a₀>(x₀: a₀, x₁: a₀): a₀;

function {:bpl} {:dfy} {:smt2} {:c} < <a₀>(x₀: a₀, x₁: a₀): bool;
function {:bpl} {:dfy} {:smt2} {:c} <= <a₀>(x₀: a₀, x₁: a₀): bool;
function {:bpl} {:dfy} {:smt2} {:c} > <a₀>(x₀: a₀, x₁: a₀): bool;
function {:bpl} {:dfy} {:smt2} {:c} >= <a₀>(x₀: a₀, x₁: a₀): bool;

function {:bpl} {:dfy} {:smt2} {:c} div(x₀: int, x₁: int): int;
function {:bpl} {:dfy} {:smt2} {:c} mod(x₀: int, x₁: int): int;
function {:bpl} {:dfy} {:smt2} /(x₀: real, x₁: real): real;
