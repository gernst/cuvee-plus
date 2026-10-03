// base types
type bool
type int

const true: bool
const false: bool

// finite container types
type seq<a>
type set<a>
type multiset<a>
type map<a,b>

// SMT-LIB array, not Dafny array
type array<a,b>

// built-in functions (fixity/precedence is built-in)
function == <a>(x$0: a, x$1: a): bool

function ite<a>(x$0: bool, x$1: a, x$2: a): a
function select<a,b>(x$0: array<a,b>, x$1: a): b
function store<a,b>(x$0: array<a,b>, x$1: a, x$2: b): array<a,b>

function !(x$0: bool): bool
function &&(x$0: bool, x$1: bool): bool
function ||(x$0: bool, x$1: bool): bool
function ==>(x$0: bool, x$1: bool): bool
function <==>(x$0: bool, x$1: bool): bool

function +(x$0: int): int
function -(x$0: int): int
function +(x$0: int, x$1: int): int
function -(x$0: int, x$1: int): int
function *(x$0: int, x$1: int): int
function /(x$0: int, x$1: int): int
function %(x$0: int, x$1: int): int

function <(x$0: int, x$1: int): bool
function <=(x$0: int, x$1: int): bool
function >(x$0: int, x$1: int): bool
function >=(x$0: int, x$1: int): bool
