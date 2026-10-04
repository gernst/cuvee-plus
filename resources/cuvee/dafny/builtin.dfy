// the built-in sorts and functions, which SMT-LIB knows, or which are eliminated before the output,
// they are parsed into the initial state and not passed on (unlike prelude.dfy)
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

// SMT-LIB array, not Dafny array
type array<a₀, a₁>

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
