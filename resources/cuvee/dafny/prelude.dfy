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
datatype {:dfy} tuple1<a₀> = tuple1(0: a₀)
datatype {:dfy} tuple2<a₀,a₁> = tuple2(0: a₀, 1: a₁)
datatype {:dfy} tuple3<a₀,a₁,a₂> = tuple3(0: a₀, 1: a₁, 2: a₂)
datatype {:dfy} tuple4<a₀,a₁,a₂,a₃> = tuple4(0: a₀, 1: a₁, 2: a₂, 3: a₃)
datatype {:dfy} tuple5<a₀,a₁,a₂,a₃,a₄> = tuple5(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄)
datatype {:dfy} tuple6<a₀,a₁,a₂,a₃,a₄,a₅> = tuple6(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅)
datatype {:dfy} tuple7<a₀,a₁,a₂,a₃,a₄,a₅,a₆> = tuple7(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆)
datatype {:dfy} tuple8<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇> = tuple8(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇)
datatype {:dfy} tuple9<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈> = tuple9(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈)
datatype {:dfy} tuple10<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉> = tuple10(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉)
datatype {:dfy} tuple11<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀> = tuple11(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀)
datatype {:dfy} tuple12<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁> = tuple12(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁)
datatype {:dfy} tuple13<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂> = tuple13(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂)
datatype {:dfy} tuple14<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃> = tuple14(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃)
datatype {:dfy} tuple15<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄> = tuple15(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄)
datatype {:dfy} tuple16<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅> = tuple16(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅)
datatype {:dfy} tuple17<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆> = tuple17(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆)
datatype {:dfy} tuple18<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆,a₁₇> = tuple18(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆, 17: a₁₇)
datatype {:dfy} tuple19<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆,a₁₇,a₁₈> = tuple19(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆, 17: a₁₇, 18: a₁₈)
datatype {:dfy} tuple20<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆,a₁₇,a₁₈,a₁₉> = tuple20(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆, 17: a₁₇, 18: a₁₈, 19: a₁₉)
