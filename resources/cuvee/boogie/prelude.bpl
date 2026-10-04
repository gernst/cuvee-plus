// base types
type bool;
type int;

// SMT-LIB array, written [a]b in Boogie
type array<a₀,a₁>;

const true: bool;
const false: bool;

// built-in functions (fixity/precedence is built-in),
// the formal parameters are named x₀, x₁, ... such that the declarations coincide with the builtin functions
function ==<a>(x₀: a, x₁: a): bool;

function ite<a>(x₀: bool, x₁: a, x₂: a): a;
function select<a, b>(x₀: [a]b, x₁: a): b;
function store<a, b>(x₀: [a]b, x₁: a, x₂: b): [a]b;

function !(x₀: bool): bool;
function &&(x₀: bool, x₁: bool): bool;
function ||(x₀: bool, x₁: bool): bool;
function ==>(x₀: bool, x₁: bool): bool;
function <==>(x₀: bool, x₁: bool): bool;

function -(x₀: int): int;
function +(x₀: int, x₁: int): int;
function -(x₀: int, x₁: int): int;
function *(x₀: int, x₁: int): int;
function div(x₀: int, x₁: int): int;
function mod(x₀: int, x₁: int): int;

function <(x₀: int, x₁: int): bool;
function <=(x₀: int, x₁: int): bool;
function >(x₀: int, x₁: int): bool;
function >=(x₀: int, x₁: int): bool;
