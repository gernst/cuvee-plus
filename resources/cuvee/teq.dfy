// the lemma database of -teq, its entry point, which -teq injects at the beginning of its output: the declarations
// that the transform and the engines refer to (Sort.trace, Fun.trace, whose type parameters and formals are numbered
// as they expect), the functions on lists that the lemmas need, and the lemmas about the traces of trace equation
// systems (one trace per strongly connected component of the variables of a loop), which the engine of -prove
// applies; started Oct 12, 2026 as the module state.dfy of -teq-state with the lemmas that the examples of
// examples/dafny/state need, copied from the modules of the per-variable form, and distincts from the former core.dfy
// (sum, count, max, min, parity and the sums are in the module aggregation, pow in arithmetic); the optional modules of
// resources/cuvee/teq are injected on demand by -include teq:<name>, the former single file of the per-variable form
// is kept in resources/cuvee/legacy/teq.dfy, not injected

datatype {:teq} {:lean} Nat = zero | succ(pred: Nat)

function {:teq} integer(n: Nat): int
{
  match n
  case zero => 0
  case succ(m) => integer(m) + 1
}

function {:teq} natural(x: int): Nat
{
  if x <= 0 then zero else succ(natural(x - 1))
}

datatype {:teq} {:lean} List<a₀> = nil | cons(head: a₀, tail: List<a₀>)

function {:teq} {:lean} length<a>(xs: List<a>): Nat

const {:teq} unspecified<a₀>: a₀

datatype {:teq} Trace<a₀> = stop(last: a₀) | step(first: a₀, rest: Trace<a₀>)

function {:teq} current<a₀>(x₀: Trace<a₀>): a₀
{
  match x₀
  case stop(x) => x
  case step(_, xs) => current(xs)
}

function {:teq} butlast<a₀>(x₀: Trace<a₀>): List<a₀>
{
  match x₀
  case stop(_) => nil
  case step(x, xs) => cons(x, butlast(xs))
}

function {:teq} counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
{
  match x₂
  case zero => stop(x₀)
  case succ(m) => step(x₀, counter(x₀ + x₁, x₁, m))
}

function {:teq} earlier<a₀>(x₀: Nat, x₁: List<a₀>): a₀
{
  match x₀, x₁
  case _, nil => unspecified
  case zero, cons(x, _) => x
  case succ(k), cons(_, xs) => earlier(k, xs)
}

function {:teq} prefix<a>(k: Nat, xs: List<a>): List<a>
{
  match k, xs
  case zero, _ => nil
  case _, nil => nil
  case succ(m), cons(x, ys) => cons(x, prefix(m, ys))
}

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

// the values of a at the keys, and the stores of the values at the keys
function {:teq} {:fold} selects<a, b>(a: array<a, b>, keys: List<a>): List<b>
{
  maps(for keys yield k :: a[k])
}

function {:teq} {:fold} stores<a, b>(a: array<a, b>, keys: List<a>, values: List<b>): Trace<array<a, b>>
{
  trace(a, for keys, values do b, k, v :: b[k := v])
}

// naturals

lemma {:rw} {:teq} natural_integer(n: Nat)
  ensures natural(integer(n)) == n

lemma {:rw} {:teq} integer_natural(x: int)
  requires 0 <= x
  ensures integer(natural(x)) == x

lemma {:rw} {:teq} zero_integer(n: Nat)
  ensures (n == zero) <==> (integer(n) == 0)

lemma {:rw} {:teq} integer_injective(m: Nat, n: Nat)
  ensures (integer(m) == integer(n)) <==> (m == n)

lemma {:rw} {:teq} natural_nonpositive(x: int)
  requires x <= 0
  ensures natural(x) == zero

// the number of iterations of an inner loop determined by its value, e.g. by the test and the exit of the loop
lemma {:rw} {:teq} integer_eq(n: Nat, x: int)
  requires 0 <= x
  ensures (integer(n) == x) <==> (n == natural(x))

// lists

lemma {:rw} {:teq} maps_identity<a>(xs: List<a>)
  ensures maps(for xs yield x :: x)
    == xs

// counters

lemma {:rw} {:teq} counter_def(i: int, c: int, n: Nat)
  ensures trace(i, for ⌊counter(0, 1, n)⌋ do x, k :: x + c)
    == counter(i, c, n)

// a variable that keeps its value in each iteration (consts_def of counters.dfy), e.g. the index of a search before it
// is found; without it, a summary lemma with a case that keeps the value matches the trace with its other cases
// unspecified
lemma {:rw} {:teq} consts_def<a>(x: a, i: int, c: int, n: Nat)
  ensures trace(x, for ⌊counter(i, c, n)⌋ do y, v :: y)
    == consts(n, x)

lemma {:rw} {:teq} maps_earlier<a>(n: Nat, xs: List<a>)
  ensures maps(for ⌊counter(0, 1, n)⌋ yield k :: earlier(natural(k), xs))
    == xs

lemma {:rw} {:teq} maps_counter_affine(a: int, b: int, i: int, c: int, n: Nat)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: a + b * v)
    == ⌊counter(a + b * i, b * c, n)⌋

lemma {:rw} {:teq} invs_counter_upper_nonnegative(m: int, n: Nat)
  requires 0 <= m
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: k < m)
    <==> integer(n) <= m

lemma {:rw} {:teq} current_counter(i: int, c: int, n: Nat)
  ensures current(counter(i, c, n))
    == i + integer(n) * c

lemma {:rw} {:teq} earlier_counter(k: Nat, i: int, c: int, n: Nat)
  ensures earlier(k, ⌊counter(i, c, n)⌋)
    == i + integer(k) * c

lemma {:rw} {:teq} prefix_counter(k: Nat, i: int, c: int, n: Nat)
  ensures prefix(k, ⌊counter(i, c, n)⌋)
    == ⌊counter(i, c, k)⌋

lemma {:rw} {:teq} occurs_counter_up(j: int, i: int, n: Nat)
  ensures occurs(j, ⌊counter(i, 1, n)⌋)
    <==> i <= j < i + integer(n)

lemma {:rw} {:teq} indexof_counter_up(j: int, i: int, n: Nat)
  requires i <= j < i + integer(n)
  ensures indexof(j, ⌊counter(i, 1, n)⌋)
    == natural(j - i)

lemma {:rw} {:teq} maps_const<a>(x: a, i: int, c: int, n: Nat)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: x)
    == ⌊consts(n, x)⌋

lemma {:rw} {:teq} prefix_maps_counter(k: Nat, i: int, c: int, n: Nat, ys: List<int>, F: (int) -> int)
  requires integer(k) <= integer(n)
  ensures prefix(k, maps(for ⌊counter(i, c, n)⌋, ys yield v, y :: F(v)))
    == maps(for ⌊counter(i, c, k)⌋ yield v :: F(v))

lemma {:rw} {:teq} butlast_counter_nil(i: int, c: int, n: Nat)
  ensures (⌊counter(i, c, n)⌋ == nil) <==> (n == zero)

lemma {:rw} {:teq} current_consts<a>(n: Nat, x: a)
  ensures current(consts(n, x))
    == x

lemma {:rw} {:teq} earlier_consts<a>(k: Nat, n: Nat, x: a)
  ensures earlier(k, ⌊consts(n, x)⌋)
    == x

// search

lemma {:rw} {:teq} not_occurs_selects_def(a: array<int, int>, x: int, i: int, n: Nat)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: a[k] != x) <==> !occurs(x, selects(a, ⌊counter(i, 1, n)⌋))

lemma {:rw} {:teq} select_not_occurs_selects(a: array<int, int>, x: int, i: int, n: Nat, k: int)
  requires !occurs(x, selects(a, ⌊counter(i, 1, n)⌋)) && i <= k < i + integer(n)
  ensures (a[k] == x) <==> false

// a choice of a loop, e.g. the numbers of iterations of an inner loop, whose values are all determined by the
// iteration constraint is a constant list, which the reads of the choice then follow (earlier_consts)
lemma {:rw} {:teq} consts_choice<a>(n: Nat, xs: List<a>, c: a)
  ensures invs(for ⌊counter(0, 1, n)⌋, xs check k, x :: x == c) <==> xs == ⌊consts(n, c)⌋

// arrays

lemma {:rw} {:teq} earlier_selects<a, b>(j: Nat, a: array<a, b>, keys: List<a>)
  ensures earlier(j, selects(a, keys))
    == a[earlier(j, keys)]

lemma {:rw} {:teq} current_stores<a, b>(k: a, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures current(stores(a, keys, values))[k]
    == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]

lemma {:rw} {:teq} earlier_stores<a, b>(k: a, j: Nat, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures earlier(j, ⌊stores(a, keys, values)⌋)[k]
    == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]
