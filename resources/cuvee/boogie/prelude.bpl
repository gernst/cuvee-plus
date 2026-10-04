// base types
type bool;
type int;
type real;

// SMT-LIB array, written [a]b in Boogie
type array<a₀, a₁>;

const true: bool;
const false: bool;

// built-in functions (fixity/precedence is built-in),
// the type parameters are named a₀, a₁, ... and the formal parameters x₀, x₁, ...,
// such that the declarations coincide with the built-in functions (see cuvee.core.Fun)
function == <a₀>(x₀: a₀, x₁: a₀): bool;

function ite<a₀>(x₀: bool, x₁: a₀, x₂: a₀): a₀;
function select<a₀, a₁>(x₀: [a₀]a₁, x₁: a₀): a₁;
function store<a₀, a₁>(x₀: [a₀]a₁, x₁: a₀, x₂: a₁): [a₀]a₁;

function !(x₀: bool): bool;
function &&(x₀: bool, x₁: bool): bool;
function ||(x₀: bool, x₁: bool): bool;
function ==>(x₀: bool, x₁: bool): bool;
function <==>(x₀: bool, x₁: bool): bool;

// arithmetic and comparison on int and real are generic,
// each application is resolved after type checking (see cuvee.core.Overload)
function - <a₀>(x₀: a₀): a₀;
function + <a₀>(x₀: a₀, x₁: a₀): a₀;
function - <a₀>(x₀: a₀, x₁: a₀): a₀;
function * <a₀>(x₀: a₀, x₁: a₀): a₀;

function < <a₀>(x₀: a₀, x₁: a₀): bool;
function <= <a₀>(x₀: a₀, x₁: a₀): bool;
function > <a₀>(x₀: a₀, x₁: a₀): bool;
function >= <a₀>(x₀: a₀, x₁: a₀): bool;

function div(x₀: int, x₁: int): int;
function mod(x₀: int, x₁: int): int;
function /(x₀: real, x₁: real): real;
