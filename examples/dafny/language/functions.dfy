// ./Cuvee.sh examples/dafny/language/functions.dfy
// function types (A, B) -> C, which associate to the right, and lambdas, whose variables are annotated with their types,
// also as arguments and results of other lambdas, and tuples as the single argument of a function type

function inc(): int -> int { (x: int) => x + 1 }

function add(): (int, int) -> int { (x: int, y: int) => x + y }

function constant(): (int -> int) -> int -> int { (f: int -> int) => (x: int) => x }

function first(): ((int, bool)) -> (int, bool) { (p: (int, bool)) => p }

lemma inc() == (y: int) => y + 1

// applications of variables and constants of function type, the parameter g shadows the function g
function twice(f: int -> int, x: int): int { f(f(x)) }

function three(): int { add(1, inc(1)) }

function g(x: int): int { x }

function shadow(g: int -> int): int { g(1) }
