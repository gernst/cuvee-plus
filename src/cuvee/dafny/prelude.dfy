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
function +(arg: int): int
function -(arg: int): int
function +(left: int, right: int): int
function -(left: int, right: int): int
function *(left: int, right: int): int
function /(left: int, right: int): int
function %(left: int, right: int): int