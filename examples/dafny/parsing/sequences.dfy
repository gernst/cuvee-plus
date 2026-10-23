// ./Cuvee.sh examples/dafny/parsing/sequences.dfy
// indexing and updates of sequences and arrays, resolved by overloading once the type of the base is known, also
// through type aliases and polymorphic functions; the type of a polymorphic constant is determined by an
// overloaded operator to its right; slices
type S = seq<int>
function alias(s: S): int { s[0] + |s| }
function array_(a: array<int,bool>, i: int): bool { a[i] && a[i := false] == a }
function id<a>(x: a): a { x }
function index_id(s: seq<int>): bool { id(s)[0] == s[1] }
function update(s: seq<bool>, i: int, j: int): bool { s[i] == s[j] && s[i := s[j]] == s }
function c<a>(): a
function constant(s: seq<int>): bool { c() + c() == s[0] }
function slices(s: seq<int>): bool { s[1..] + s[..1] == [s[0]] + s[1..|s|] }
