// the lemma database of -teq, its entry point, which -teq injects at the beginning of its output: the declarations that
// the transform and the engines refer to (Sort.trace, Fun.trace, whose type parameters and formals are numbered as they
// expect), the functions on lists that the lemmas need, and the lemmas about the traces of trace equation systems,
// which the engine of -prove applies; the optional modules of resources/cuvee/teq are injected after it by
// -include teq:<name>

datatype {:teq} {:lean} List<a₀> = nil | cons(head: a₀, tail: List<a₀>)

function {:teq} {:lean} length<a>(xs: List<a>): int

const {:teq} unspecified<a₀>: a₀

datatype {:teq} Trace<a₀> = stop(last: a₀) | step(first: a₀, rest: Trace<a₀>)

function {:rw} {:teq} current<a₀>(x₀: Trace<a₀>): a₀
{
  match x₀
  case stop(x) => x
  case step(_, xs) => current(xs)
}

function {:rw} {:teq} butlast<a₀>(x₀: Trace<a₀>): List<a₀>
{
  match x₀
  case stop(_) => nil
  case step(x, xs) => cons(x, butlast(xs))
}

// the counts, lengths and positions are integers; the definitions clamp: a count that is not positive is no step, a
// negative position reads no element
function {:teq} counter(x₀: int, x₁: int, x₂: int): Trace<int>
{
  if x₂ <= 0 then stop(x₀) else step(x₀, counter(x₀ + x₁, x₁, x₂ - 1))
}

function {:rw} {:teq} earlier<a₀>(x₀: int, x₁: List<a₀>): a₀
{
  match x₁
  case nil => unspecified
  case cons(x, xs) => if x₀ < 0 then unspecified else if x₀ == 0 then x else earlier(x₀ - 1, xs)
}

function {:rw} {:teq} prefix<a>(k: int, xs: List<a>): List<a>
{
  match xs
  case nil => nil
  case cons(x, ys) => if k <= 0 then nil else cons(x, prefix(k - 1, ys))
}

function {:rw} {:teq} occurs<a>(x: a, xs: List<a>): bool
{
  match xs
  case nil => false
  case cons(y, ys) => y == x || occurs(x, ys)
}

function {:rw} {:teq} indexof<a>(x: a, xs: List<a>): int
{
  match xs
  case nil => 0
  case cons(y, ys) => if occurs(x, ys) then indexof(x, ys) + 1 else 0
}

// whether a list has no duplicates
function {:rw} {:teq} distincts<a>(xs: List<a>): bool
{
  match xs
  case nil => true
  case cons(y, ys) => !occurs(y, ys) && distincts(ys)
}

// consts(n, v) is the trace v, ..., v of n steps
function {:teq} consts<a>(n: int, v: a): Trace<a>
{
  if n <= 0 then stop(v) else step(v, consts(n - 1, v))
}

// the cut of a predicate G that holds on a prefix of [l, h): the first index where it fails, h if none (l if the
// interval is empty); a predicate H that holds on a suffix has the cut of its negation, the first index where H
// holds; by the search of the n indices from l, cutFrom; neither is a rule of the engines
function {:teq} cutFrom(G: int -> bool, l: int, n: int): int
{
  if n <= 0 then l else if G(l) then cutFrom(G, l + 1, n - 1) else l
}

function {:teq} cut(G: int -> bool, l: int, h: int): int
{
  cutFrom(G, l, h - l)
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

// lists

lemma {:rw} {:teq} maps_identity<a>(xs: List<a>)
  ensures maps(for xs yield x :: x)
    == xs

// counters

lemma {:rw} {:teq} counter_def(i: int, c: int, n: int)
  ensures trace(i, for ⌊counter(0, 1, n)⌋ do x, k :: x + c)
    == counter(i, c, n)

// a variable that keeps its value in each iteration, e.g. the index of a search before it
// is found; without it, a summary lemma with a case that keeps the value matches the trace with its other cases
// unspecified
lemma {:rw} {:teq} consts_def<a>(x: a, i: int, c: int, n: int)
  ensures trace(x, for ⌊counter(i, c, n)⌋ do y, v :: y)
    == consts(n, x)

// the values that a loop of n iterations reads from xs at its iterations, which are within xs, as all reads of
// earlier are (n <= length(xs)), not the whole list: the list may be that of an earlier loop with more iterations
lemma {:rw} {:teq} maps_earlier<a>(n: int, xs: List<a>)
  ensures maps(for ⌊counter(0, 1, n)⌋ yield k :: earlier(k, xs))
    == prefix(n, xs)

// a read within such a prefix reads the list, e.g. a[x] == b[x] where b is a copy of a by a loop, whose values are
// the prefix, while the read of a is of the list
// (from standard_copy*_ground, standard_strcpy_*, standard_compareModified_ground, standard_two_index_01)
lemma {:rw} {:teq} earlier_prefix<a>(j: int, k: int, xs: List<a>)
  requires j < k
  ensures earlier(j, prefix(k, xs))
    == earlier(j, xs)

lemma {:rw} {:teq} maps_counter_affine(a: int, b: int, i: int, c: int, n: int)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: a + b * v)
    == ⌊counter(a + b * i, b * c, n)⌋

// the same without a constant summand, which the pattern a + b * v does not match (a sum is needed for a = 0)
// (from mbpr2)
lemma {:rw} {:teq} maps_counter_scale(b: int, i: int, c: int, n: int)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: b * v)
    == ⌊counter(b * i, b * c, n)⌋

lemma {:rw} {:teq} invs_const(b: bool, i: int, c: int, n: int)
  ensures invs(for ⌊counter(i, c, n)⌋ check v :: b)
    <==> n <= 0 || b

lemma {:rw} {:teq} invs_counter_lower(m: int, i: int, c: int, n: int)
  ensures invs(for ⌊counter(i, c, n)⌋ check k :: m <= k)
    <==> n <= 0 || m <= i && m <= i + (n - 1) * c

lemma {:rw} {:teq} distincts_counter(i: int, c: int, n: int)
  requires c != 0
  ensures distincts(⌊counter(i, c, n)⌋)

lemma {:rw} {:teq} invs_counter_upper_nonnegative(m: int, n: int)
  requires 0 <= m
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: k < m)
    <==> n <= m

lemma {:rw} {:teq} invs_counter_upper(m: int, i: int, c: int, n: int)
  ensures invs(for ⌊counter(i, c, n)⌋ check k :: k < m)
    <==> n <= 0 || i < m && i + (n - 1) * c < m

// for a count that is not negative, which TEQ states for the number of iterations of every loop
lemma {:rw} {:teq} current_counter(i: int, c: int, n: int)
  requires 0 <= n
  ensures current(counter(i, c, n))
    == i + n * c

lemma {:rw} {:teq} earlier_counter(k: int, i: int, c: int, n: int)
  ensures earlier(k, ⌊counter(i, c, n)⌋)
    == i + k * c

lemma {:rw} {:teq} prefix_counter(k: int, i: int, c: int, n: int)
  ensures prefix(k, ⌊counter(i, c, n)⌋)
    == ⌊counter(i, c, k)⌋

lemma {:rw} {:teq} occurs_counter_up(j: int, i: int, n: int)
  ensures occurs(j, ⌊counter(i, 1, n)⌋)
    <==> i <= j < i + n

lemma {:rw} {:teq} indexof_counter_up(j: int, i: int, n: int)
  requires i <= j < i + n
  ensures indexof(j, ⌊counter(i, 1, n)⌋)
    == j - i

lemma {:rw} {:teq} maps_const<a>(x: a, i: int, c: int, n: int)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: x)
    == ⌊consts(n, x)⌋

lemma {:rw} {:teq} prefix_maps_counter(k: int, i: int, c: int, n: int, ys: List<int>, F: (int) -> int)
  requires k <= n
  ensures prefix(k, maps(for ⌊counter(i, c, n)⌋, ys yield v, y :: F(v)))
    == maps(for ⌊counter(i, c, k)⌋ yield v :: F(v))

lemma {:rw} {:teq} butlast_counter_nil(i: int, c: int, n: int)
  ensures (⌊counter(i, c, n)⌋ == nil) <==> (n <= 0)

// e.g. the iterations of a loop that runs once against a constant trace
lemma {:rw} {:teq} butlast_counter_consts(i: int, c: int, n: int, v: int)
  ensures (⌊counter(i, c, n)⌋ == ⌊consts(n, v)⌋) <==> (n <= 0 || i == v && (n <= 1 || c == 0))

lemma {:rw} {:teq} current_consts<a>(n: int, x: a)
  ensures current(consts(n, x))
    == x

lemma {:rw} {:teq} earlier_consts<a>(k: int, n: int, x: a)
  ensures earlier(k, ⌊consts(n, x)⌋)
    == x

// the lengths of the lists of the database, by their definitions, from the simpler to the more specific; the counts
// clamp, hence a count that is not negative; a list of length 0 is the empty list
lemma {:rw} {:teq} length_nil<a>()
  ensures length(nil as List<a>) == 0

lemma {:rw} {:teq} length_cons<a>(x: a, xs: List<a>)
  ensures length(cons(x, xs)) == length(xs) + 1

lemma {:rw} {:teq} length_eq_zero<a>(xs: List<a>)
  ensures (length(xs) == 0) <==> (xs == nil)

lemma {:rw} {:teq} length_counter(i: int, c: int, n: int)
  requires 0 <= n
  ensures length(⌊counter(i, c, n)⌋) == n

lemma {:rw} {:teq} length_consts<a>(n: int, x: a)
  requires 0 <= n
  ensures length(⌊consts(n, x)⌋) == n

lemma {:rw} {:teq} length_prefix<a>(k: int, xs: List<a>)
  requires 0 <= k <= length(xs)
  ensures length(prefix(k, xs)) == k

// a prefix at least as long as the list is the list
lemma {:rw} {:teq} prefix_length<a>(k: int, xs: List<a>)
  requires length(xs) <= k
  ensures prefix(k, xs) == xs

lemma {:rw} {:teq} length_maps<a, b>(xs: List<a>, F: (a) -> b)
  ensures length(maps(for xs yield x :: F(x))) == length(xs)

lemma {:rw} {:teq} length_maps_deps<a, b, c>(xs: List<a>, ys: List<b>, F: (a, b) -> c)
  requires length(ys) == length(xs)
  ensures length(maps(for xs, ys yield x, y :: F(x, y))) == length(xs)

lemma {:rw} {:teq} length_selects<a, b>(a: array<a, b>, keys: List<a>)
  ensures length(selects(a, keys)) == length(keys)

lemma {:rw} {:teq} length_stores<a, b>(a: array<a, b>, keys: List<a>, values: List<b>)
  requires length(values) == length(keys)
  ensures length(⌊stores(a, keys, values)⌋) == length(keys)

// a choice of a loop, e.g. the numbers of iterations of an inner loop, whose values are all determined by the
// iteration constraint is a constant list, which the reads of the choice then follow (earlier_consts)
lemma {:rw} {:teq} consts_choice<a>(n: int, xs: List<a>, c: a)
  ensures invs(for ⌊counter(0, 1, n)⌋, xs check k, x :: x == c) <==> xs == ⌊consts(n, c)⌋

// arrays

// no keys select no values
// (from examples/dafny/algorithms/prefix_sums.dfy; unused on SV-COMP)
lemma {:rw} {:teq} selects_nil<a, b>(a: array<a, b>)
  ensures selects(a, nil)
    == nil

lemma {:rw} {:teq} earlier_selects<a, b>(j: int, a: array<a, b>, keys: List<a>)
  ensures earlier(j, selects(a, keys))
    == a[earlier(j, keys)]

lemma {:rw} {:teq} current_stores<a, b>(k: a, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures current(stores(a, keys, values))[k]
    == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]

lemma {:rw} {:teq} earlier_stores<a, b>(k: a, j: int, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures earlier(j, ⌊stores(a, keys, values)⌋)[k]
    == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]
