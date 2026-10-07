// the prelude of Dafny, which is parsed into the initial state and injected at the beginning of the commands,
// where each declaration names the languages that it is part of by their file extensions, {:dfy}, {:bpl}, {:smt2}, {:c},
// and the output in one of these languages drops it (see cuvee.pipe.Printer.filter),
// e.g. the tuples are part of Dafny, but must be declared as datatypes in SMT-LIB;
// the definitions of parallel composition are injected with the option -hybrid (see hybrid.dfy)

// base types
type {:dfy} {:bpl} {:smt2} {:c} bool
type {:dfy} {:bpl} {:smt2} {:c} int
type {:dfy} {:bpl} {:smt2} real
type {:dfy} {:smt2} string

const {:dfy} {:bpl} {:smt2} {:c} true: bool
const {:dfy} {:bpl} {:smt2} {:c} false: bool

// finite container types
type {:dfy} {:bpl} {:smt2} seq<a₀>
type {:dfy} {:smt2} set<a₀>
type {:dfy} multiset<a₀>
type {:dfy} map<a₀, a₁>

// SMT-LIB array, not Dafny array
type {:dfy} {:bpl} {:smt2} {:c} array<a₀, a₁>

// built-in functions (fixity/precedence is built-in),
// the type parameters are named a₀, a₁, ... and the formal parameters x₀, x₁, ...,
// such that the declarations coincide with the built-in functions (see cuvee.core.Fun),
// arithmetic and comparison are generic, each application is resolved after type checking (see cuvee.core.Overload),
// unary + is the identity, which is dropped by the parser
function {:dfy} {:bpl} {:smt2} {:c} == <a₀>(x₀: a₀, x₁: a₀): bool

function {:dfy} {:bpl} {:smt2} {:c} ite<a₀>(x₀: bool, x₁: a₀, x₂: a₀): a₀
// indexing and updates of arrays and sequences, s[i] and s[i := v], resolved like arithmetic
function {:dfy} {:bpl} {:smt2} {:c} select<a₀, a₁, a₂>(x₀: a₀, x₁: a₁): a₂
function {:dfy} {:bpl} {:smt2} {:c} store<a₀, a₁, a₂>(x₀: a₀, x₁: a₁, x₂: a₂): a₀

// negation, which is also the complement of bitvectors, resolved like arithmetic
function {:dfy} {:bpl} {:smt2} {:c} ! <a₀>(x₀: a₀): a₀
function {:dfy} {:bpl} {:smt2} {:c} &&(x₀: bool, x₁: bool): bool
function {:dfy} {:bpl} {:smt2} {:c} ||(x₀: bool, x₁: bool): bool
function {:dfy} {:bpl} {:smt2} {:c} ==>(x₀: bool, x₁: bool): bool
function {:dfy} {:bpl} {:smt2} {:c} <==>(x₀: bool, x₁: bool): bool

function {:dfy} {:bpl} {:smt2} {:c} - <a₀>(x₀: a₀): a₀
function {:dfy} {:bpl} {:smt2} {:c} + <a₀>(x₀: a₀, x₁: a₀): a₀
// the second argument of - may differ, m - s removes the keys s from a map m (see cuvee.core.Overload)
function {:dfy} {:bpl} {:smt2} {:c} - <a₀,a₁>(x₀: a₀, x₁: a₁): a₀
function {:dfy} {:bpl} {:smt2} {:c} * <a₀>(x₀: a₀, x₁: a₀): a₀
function {:dfy} {:bpl} {:smt2} {:c} / <a₀>(x₀: a₀, x₁: a₀): a₀
function {:dfy} {:bpl} {:smt2} {:c} % <a₀>(x₀: a₀, x₁: a₀): a₀

// bitwise and and exclusive or of bitvectors, which never leave the frontend, like the other generic operators
function {:dfy} {:bpl} {:smt2} & <a₀>(x₀: a₀, x₁: a₀): a₀
function {:dfy} {:bpl} {:smt2} ^ <a₀>(x₀: a₀, x₁: a₀): a₀

// the conversions e as int and e as bv8 of integers and bitvectors, whose result type is the target
function {:dfy} {:bpl} {:smt2} {:c} as_int<a₀>(x₀: a₀): int
function {:dfy} {:bpl} {:smt2} as_bv<a₀, a₁>(x₀: a₀): a₁

function {:dfy} {:bpl} {:smt2} {:c} < <a₀>(x₀: a₀, x₁: a₀): bool
function {:dfy} {:bpl} {:smt2} {:c} <= <a₀>(x₀: a₀, x₁: a₀): bool
function {:dfy} {:bpl} {:smt2} {:c} > <a₀>(x₀: a₀, x₁: a₀): bool
function {:dfy} {:bpl} {:smt2} {:c} >= <a₀>(x₀: a₀, x₁: a₀): bool

// tuples, where the components are numbered from 0 as in Dafny,
// the selectors are qualified with the type since selector names must be unique
datatype {:dfy} tuple₁<a₀> = tuple₁(0: a₀)
datatype {:dfy} tuple₂<a₀,a₁> = tuple₂(0: a₀, 1: a₁)
datatype {:dfy} tuple₃<a₀,a₁,a₂> = tuple₃(0: a₀, 1: a₁, 2: a₂)
datatype {:dfy} tuple₄<a₀,a₁,a₂,a₃> = tuple₄(0: a₀, 1: a₁, 2: a₂, 3: a₃)
datatype {:dfy} tuple₅<a₀,a₁,a₂,a₃,a₄> = tuple₅(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄)
datatype {:dfy} tuple₆<a₀,a₁,a₂,a₃,a₄,a₅> = tuple₆(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅)
datatype {:dfy} tuple₇<a₀,a₁,a₂,a₃,a₄,a₅,a₆> = tuple₇(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆)
datatype {:dfy} tuple₈<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇> = tuple₈(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇)
datatype {:dfy} tuple₉<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈> = tuple₉(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈)
datatype {:dfy} tuple₁₀<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉> = tuple₁₀(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉)

// function types (A₁, ..., Aₙ) -> R of 1 to 10 arguments, whose last type parameter is the result (see cuvee.core.Arrow),
// which are higher-order ({:ho}), whose declarations are not passed to solvers
type {:dfy} {:ho} arrow₁<a₀,a₁>
type {:dfy} {:ho} arrow₂<a₀,a₁,a₂>
type {:dfy} {:ho} arrow₃<a₀,a₁,a₂,a₃>
type {:dfy} {:ho} arrow₄<a₀,a₁,a₂,a₃,a₄>
type {:dfy} {:ho} arrow₅<a₀,a₁,a₂,a₃,a₄,a₅>
type {:dfy} {:ho} arrow₆<a₀,a₁,a₂,a₃,a₄,a₅,a₆>
type {:dfy} {:ho} arrow₇<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇>
type {:dfy} {:ho} arrow₈<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈>
type {:dfy} {:ho} arrow₉<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉>
type {:dfy} {:ho} arrow₁₀<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀>

// the applications f(x₁, ..., xₙ) of function values (see cuvee.core.Apply), which are higher-order ({:ho}),
// whose declarations are not passed to solvers, since SMT-LIB has no representation of function types yet (see TODO.md)
function {:dfy} {:ho} apply₁<a₀,a₁>(x₀: arrow₁<a₀,a₁>, x₁: a₀): a₁
function {:dfy} {:ho} apply₂<a₀,a₁,a₂>(x₀: arrow₂<a₀,a₁,a₂>, x₁: a₀, x₂: a₁): a₂
function {:dfy} {:ho} apply₃<a₀,a₁,a₂,a₃>(x₀: arrow₃<a₀,a₁,a₂,a₃>, x₁: a₀, x₂: a₁, x₃: a₂): a₃
function {:dfy} {:ho} apply₄<a₀,a₁,a₂,a₃,a₄>(x₀: arrow₄<a₀,a₁,a₂,a₃,a₄>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃): a₄
function {:dfy} {:ho} apply₅<a₀,a₁,a₂,a₃,a₄,a₅>(x₀: arrow₅<a₀,a₁,a₂,a₃,a₄,a₅>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃, x₅: a₄): a₅
function {:dfy} {:ho} apply₆<a₀,a₁,a₂,a₃,a₄,a₅,a₆>(x₀: arrow₆<a₀,a₁,a₂,a₃,a₄,a₅,a₆>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃, x₅: a₄, x₆: a₅): a₆
function {:dfy} {:ho} apply₇<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇>(x₀: arrow₇<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃, x₅: a₄, x₆: a₅, x₇: a₆): a₇
function {:dfy} {:ho} apply₈<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈>(x₀: arrow₈<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃, x₅: a₄, x₆: a₅, x₇: a₆, x₈: a₇): a₈
function {:dfy} {:ho} apply₉<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉>(x₀: arrow₉<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃, x₅: a₄, x₆: a₅, x₇: a₆, x₈: a₇, x₉: a₈): a₉
function {:dfy} {:ho} apply₁₀<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀>(x₀: arrow₁₀<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀>, x₁: a₀, x₂: a₁, x₃: a₂, x₄: a₃, x₅: a₄, x₆: a₅, x₇: a₆, x₈: a₇, x₉: a₈, x₁₀: a₉): a₁₀
