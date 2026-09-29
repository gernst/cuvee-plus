// base types
type bool
type int

// finite container types
type seq<a>
type set<a>
type multiset<a>
type map<a,b>

// SMT-LIB array, not Dafny array
type array<a,b>

// built-in functions (fixity/precedence is built-in)
function == <a>(left: a, right: a): bool

function ite<a>(test: bool, left: a, right: a): a
function select<a,b>(base: array<a,b>, index: a): b
function store<a,b>(base: array<a,b>, index: a, value: b): array<a,b>

function !(arg: bool): bool
function &&(left: bool, right: bool): bool
function ||(left: bool, right: bool): bool
function ==>(left: bool, right: bool): bool
function <==>(left: bool, right: bool): bool

function +(arg: int): int
function -(arg: int): int
function +(left: int, right: int): int
function -(left: int, right: int): int
function *(left: int, right: int): int
function /(left: int, right: int): int
function %(left: int, right: int): int