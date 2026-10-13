// the core of the lemma database of -teq, the first module of resources/cuvee/teq (extracted from teq.dfy on Oct 11,
// 2026, which is kept but not injected): the types of naturals, lists, and traces, the functions on them that the
// transform and the simplifier refer to (see cuvee.core.Sort.trace and cuvee.core.Fun.trace, whose type parameters and
// formals are numbered as there, Fun.formals), the basic functions on lists that the other modules use, and the
// definitions that several modules share (sum, parity, max, min, count, pow, and the reads selects of an array at a
// list of keys), since the modules would otherwise depend on each other cyclically (counters uses sum, aggregation uses
// selects, arrays uses sum); no lemmas: the other modules (arithmetic, counters, aggregation, arrays, search, nested,
// sorting) assume these declarations and are injected after it, in that order, which is the order in which the rules
// are tried

// natural numbers, the numbers of iterations and the indices of sequences, with their values as integers;
// Nat and List are those of Lean ({:lean})
datatype {:teq} {:lean} Nat = zero | succ(pred: Nat)

function {:teq} integer(n: Nat): int
{
  match n
  case zero => 0
  case succ(m) => integer(m) + 1
}

// the natural number of an integer, zero for those that are not positive
function {:teq} natural(x: int): Nat
{
  if x <= 0 then zero else succ(natural(x - 1))
}

// lists, the sequences of values of the dependencies of trace equation systems
datatype {:teq} {:lean} List<a₀> = nil | cons(head: a₀, tail: List<a₀>)

// the length of a list, List.length of Lean ({:lean}), with which the Lean printer states that the dependencies of the
// combinators of a lemma have the length of the loop (see teq.lean); declared only, the simplifier has no rules on it
function {:teq} {:lean} length<a>(xs: List<a>): Nat

// a value that is not specified, e.g. of the elements outside of a list
const {:teq} unspecified<a₀>: a₀

// the type and the functions of Fun.trace, whose type parameters and formals are numbered as there (Fun.formals)

// the traces of trace equation systems, the values of a variable at the loop head: the value before an iteration
// followed by the trace of the remaining iterations (step), or the last value (stop)
datatype {:teq} Trace<a₀> = stop(last: a₀) | step(first: a₀, rest: Trace<a₀>)

// the last element of a trace
function {:teq} current<a₀>(x₀: Trace<a₀>): a₀
{
  match x₀
  case stop(x) => x
  case step(_, xs) => current(xs)
}

// all but the last element of a trace, written ⌊X⌋
function {:teq} butlast<a₀>(x₀: Trace<a₀>): List<a₀>
{
  match x₀
  case stop(_) => nil
  case step(x, xs) => cons(x, butlast(xs))
}

// counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps
function {:teq} counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
{
  match x₂
  case zero => stop(x₀)
  case succ(m) => step(x₀, counter(x₀ + x₁, x₁, m))
}

// the elements of lists, unspecified outside of them
function {:teq} earlier<a₀>(x₀: Nat, x₁: List<a₀>): a₀
{
  match x₀, x₁
  case _, nil => unspecified
  case zero, cons(x, _) => x
  case succ(k), cons(_, xs) => earlier(k, xs)
}

// the first k elements of a list
function {:teq} prefix<a>(k: Nat, xs: List<a>): List<a>
{
  match k, xs
  case zero, _ => nil
  case _, nil => nil
  case succ(m), cons(x, ys) => cons(x, prefix(m, ys))
}

// whether x occurs in a list, and the index of its last occurrence (unspecified otherwise, zero here)
function {:teq} occurs<a>(x: a, xs: List<a>): bool
{
  match xs
  case nil => false
  case cons(y, ys) => y == x || occurs(x, ys)
}

function {:teq} indexof<a>(x: a, xs: List<a>): Nat
{
  match xs
  case nil => zero
  case cons(y, ys) => if occurs(x, ys) then succ(indexof(x, ys)) else zero
}

// whether a list has no duplicates
function {:teq} distincts<a>(xs: List<a>): bool
{
  match xs
  case nil => true
  case cons(y, ys) => !occurs(y, ys) && distincts(ys)
}

// consts(n, v) is the trace v, ..., v of n steps
function {:teq} consts<a>(n: Nat, v: a): Trace<a>
{
  match n
  case zero => stop(v)
  case succ(m) => step(v, consts(m, v))
}

// the functions of lists and integers that several modules use, and selects, the values of an array at the keys,
// the fold of a map (see arrays.dfy)

// the sum of a list
function {:teq} sum(values: List<int>): int
{
  match values
  case nil => 0
  case cons(v, vs) => v + sum(vs)
}

// the parity of a list, the number of even minus the number of odd elements
function {:teq} parity(values: List<int>): int
{
  match values
  case nil => 0
  case cons(v, vs) => (if v % 2 == 0 then 1 else -1) + parity(vs)
}

// the maximum and the minimum
function {:teq} max(m: int, n: int): int
{
  if m <= n then n else m
}

function {:teq} min(m: int, n: int): int
{
  if m <= n then m else n
}

// the number of occurrences of a value in a list
function {:teq} count<a>(e: a, vs: List<a>): int
{
  match vs
  case nil => 0
  case cons(v, ws) => (if v == e then 1 else 0) + count(e, ws)
}

// powers, which are not unfolded
function {:teq} pow(c: int, n: Nat): int
{
  match n
  case zero => 1
  case succ(m) => c * pow(c, m)
}

// the values of a at the keys
function {:teq} {:fold} selects<a, b>(a: array<a, b>, keys: List<a>): List<b>
{
  maps(for keys yield k :: a[k])
}
