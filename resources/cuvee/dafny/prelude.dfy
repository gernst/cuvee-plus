// base types
type bool
type int
type real

const true: bool
const false: bool

// finite container types
type seq<a₀>
type set<a₀>
type multiset<a₀>
type map<a₀, a₁>

// the traces of trace equation systems, the values of a variable at the loop head (see cuvee.core.Sort.trace)
type Trace<a₀>

// the events of parallel components, values sent and received on channels,
// the global history of events, e.g. var history: seq<event<int>>;
// and the methods send and receive are declared by the input (see examples/dafny/par.dfy)
type chan
datatype event<a₀> = event(chan: chan, value: a₀)

// SMT-LIB array, not Dafny array
type array<a₀, a₁>

// tuples, where the components are numbered from 0 as in Dafny,
// the selectors are qualified with the type since selector names must be unique
datatype tuple1<a₀> = tuple1(0: a₀)
datatype tuple2<a₀,a₁> = tuple2(0: a₀, 1: a₁)
datatype tuple3<a₀,a₁,a₂> = tuple3(0: a₀, 1: a₁, 2: a₂)
datatype tuple4<a₀,a₁,a₂,a₃> = tuple4(0: a₀, 1: a₁, 2: a₂, 3: a₃)
datatype tuple5<a₀,a₁,a₂,a₃,a₄> = tuple5(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄)
datatype tuple6<a₀,a₁,a₂,a₃,a₄,a₅> = tuple6(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅)
datatype tuple7<a₀,a₁,a₂,a₃,a₄,a₅,a₆> = tuple7(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆)
datatype tuple8<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇> = tuple8(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇)
datatype tuple9<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈> = tuple9(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈)
datatype tuple10<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉> = tuple10(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉)
datatype tuple11<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀> = tuple11(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀)
datatype tuple12<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁> = tuple12(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁)
datatype tuple13<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂> = tuple13(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂)
datatype tuple14<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃> = tuple14(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃)
datatype tuple15<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄> = tuple15(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄)
datatype tuple16<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅> = tuple16(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅)
datatype tuple17<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆> = tuple17(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆)
datatype tuple18<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆,a₁₇> = tuple18(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆, 17: a₁₇)
datatype tuple19<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆,a₁₇,a₁₈> = tuple19(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆, 17: a₁₇, 18: a₁₈)
datatype tuple20<a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂,a₁₃,a₁₄,a₁₅,a₁₆,a₁₇,a₁₈,a₁₉> = tuple20(0: a₀, 1: a₁, 2: a₂, 3: a₃, 4: a₄, 5: a₅, 6: a₆, 7: a₇, 8: a₈, 9: a₉, 10: a₁₀, 11: a₁₁, 12: a₁₂, 13: a₁₃, 14: a₁₄, 15: a₁₅, 16: a₁₆, 17: a₁₇, 18: a₁₈, 19: a₁₉)

// built-in functions (fixity/precedence is built-in),
// the type parameters are named a₀, a₁, ... and the formal parameters x₀, x₁, ...,
// such that the declarations coincide with the built-in functions (see cuvee.core.Fun),
// arithmetic and comparison are generic, each application is resolved after type checking (see cuvee.core.Overload),
// unary + is the identity, which is dropped by the parser
function == <a₀>(x₀: a₀, x₁: a₀): bool

function ite<a₀>(x₀: bool, x₁: a₀, x₂: a₀): a₀
// indexing and updates of arrays and sequences, s[i] and s[i := v], resolved like arithmetic
function select<a₀, a₁, a₂>(x₀: a₀, x₁: a₁): a₂
function store<a₀, a₁, a₂>(x₀: a₀, x₁: a₁, x₂: a₂): a₀

function !(x₀: bool): bool
function &&(x₀: bool, x₁: bool): bool
function ||(x₀: bool, x₁: bool): bool
function ==>(x₀: bool, x₁: bool): bool
function <==>(x₀: bool, x₁: bool): bool

function - <a₀>(x₀: a₀): a₀
function + <a₀>(x₀: a₀, x₁: a₀): a₀
function - <a₀>(x₀: a₀, x₁: a₀): a₀
function * <a₀>(x₀: a₀, x₁: a₀): a₀
function / <a₀>(x₀: a₀, x₁: a₀): a₀
function % <a₀>(x₀: a₀, x₁: a₀): a₀

function < <a₀>(x₀: a₀, x₁: a₀): bool
function <= <a₀>(x₀: a₀, x₁: a₀): bool
function > <a₀>(x₀: a₀, x₁: a₀): bool
function >= <a₀>(x₀: a₀, x₁: a₀): bool
