// the lemma database of -teq, which is injected at the beginning of its output:
// the type of traces and the functions on them (see cuvee.core.Sort.trace and cuvee.core.Fun.trace),
// which exist only with -teq, and lemmas about them, which are rewrite rules of the simplifier ({:rw}),
// the simplifier is expected to prove the goals of -teq on its own, not the solvers,
// functions that produce traces are plural (sums, counts), their scalar counterparts singular (sum, count),
// the lemmas are grouped by the function of their left-hand side

// the type and the functions of Fun.trace, whose type parameters and formals are numbered as there (Fun.formals)

// the traces of trace equation systems, the values of a variable at the loop head
type Trace<a₀>
// all but the last element of a trace, written ⌊X⌋
function butlast<a₀>(x₀: Trace<a₀>): seq<a₀>
// counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
// the last element of a trace
function current<a₀>(x₀: Trace<a₀>): a₀
// the number of steps of a trace, which is one less than the number of its elements
function steps<a₀>(x₀: Trace<a₀>): int
// the length of a sequence
function length<a₀>(x₀: seq<a₀>): int
// the elements of sequences
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// the first k elements of a sequence
function prefix<a>(k: int, xs: seq<a>): seq<a>

// whether x occurs in a sequence, and the index of its last occurrence (unspecified otherwise)
function occurs<a>(x: a, xs: seq<a>): bool
function indexof<a>(x: a, xs: seq<a>): int

// whether a sequence has no duplicates
function distincts<a>(xs: seq<a>): bool

// consts(n, v) is the trace v, ..., v of n steps
function consts<a>(n: int, v: a): Trace<a>

// selects(a, keys) are the values of a at the keys,
// stores(a, keys, values) is the trace of the successive stores of the values at the keys into a
function selects<a, b>(a: array<a, b>, keys: seq<a>): seq<b>
function stores<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>): Trace<array<a, b>>

// shifts(a, keys, d) is the trace of the successive copies a[k] := a[k + d] for the keys,
// which is modeled for increasing keys and nonnegative offsets only, where the entries read are not yet modified
function shifts(a: array<int, int>, keys: seq<int>, d: int): Trace<array<int, int>>

// the prefix sums of a sequence starting with an initial value, and the sum of a sequence
function sums(x: int, values: seq<int>): Trace<int>
function sum(values: seq<int>): int

// the prefix parities (the number of even minus the number of odd elements) starting with an initial value,
// and the parity of a sequence
function parities(x: int, values: seq<int>): Trace<int>
function parity(values: seq<int>): int

// the prefix maxima and minima starting with an initial value
function maxs(x: int, values: seq<int>): Trace<int>
function mins(x: int, values: seq<int>): Trace<int>

function max(m: int, n: int): int
{
  if m <= n then n else m
}

function min(m: int, n: int): int
{
  if m <= n then m else n
}

// the number of occurrences of a value, counted from an initial value, and in a sequence
function counts<a>(x: int, e: a, vs: seq<a>): Trace<int>
function count<a>(e: a, vs: seq<a>): int

// traces

// a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
lemma {:rw} {:free} forall i: int, c: int, K: Trace<int> ::
  trace(i, for ⌊K⌋ do x, k => x + c)
    == counter(i, c, steps(K))

lemma <a, b> {:rw} {:free} forall x: a, xs: seq<b> ::
  trace(x, for xs do y, v => y)
    == consts(length(xs), x)

lemma <a, b> {:rw} {:free} forall a: array<a, b>, keys: seq<a>, values: seq<b> ::
  trace(a, for keys, values do b, k, v => b[k := v])
    == stores(a, keys, values)

// each key is visited once only if they are distinct, hence a[k] is still the initial value
lemma <a> {:rw} {:free} forall a: array<a, int>, keys: seq<a>, bs: seq<int>, cs: seq<int> ::
  if distincts(keys)
  then trace(a, for keys, bs, cs do b, k, x, y => b[k := x * b[k] + y])
         == trace(a, for keys, bs, cs do b, k, x, y => b[k := x * a[k] + y])

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int>, d: int ::
  trace(a, for keys do b, k => b[k := b[k + d]])
    == shifts(a, keys, d)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do s, v => s + v)
    == sums(x, values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do s, v => if v % 2 == 0 then s + 1, if v % 2 != 0 then s - 1)
    == parities(x, values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do m, v => if m < v then v, if v <= m then m)
    == maxs(x, values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do m, v => if m > v then v, if v >= m then m)
    == mins(x, values)

lemma <a> {:rw} {:free} forall x: int, e: a, vs: seq<a> ::
  trace(x, for vs do y, v => if v == e then y + 1, if v != e then y)
    == counts(x, e, vs)

// on booleans, the guards are the values themselves; the occurrences of false come first,
// since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
lemma {:rw} {:free} forall x: int, bs: seq<bool> ::
  trace(x, for bs do y, b => if !b then y + 1, if b then y)
    == counts(x, false, bs)

lemma {:rw} {:free} forall x: int, bs: seq<bool> ::
  trace(x, for bs do y, b => if b then y + 1, if !b then y)
    == counts(x, true, bs)

// maps

lemma <a> {:rw} {:free} forall n: int, xs: seq<a> ::
  maps(for ⌊counter(0, 1, n)⌋ yield k => earlier(k, xs))
    == xs

lemma {:rw} {:free} forall a: int, b: int, i: int, c: int, n: int ::
  maps(for ⌊counter(i, c, n)⌋ yield v => a + b * v)
    == ⌊counter(a + b * i, b * c, n)⌋

lemma <a, b> {:rw} {:free} forall x: a, xs: seq<b> ::
  maps(for xs yield v => x)
    == ⌊consts(length(xs), x)⌋

lemma <a, b> {:rw} {:free} forall a: array<a, b>, keys: seq<a> ::
  maps(for keys yield k => a[k])
    == selects(a, keys)

// invs

lemma {:rw} {:free} forall m: int, i: int, c: int, n: int ::
  invs(for ⌊counter(i, c, n)⌋ check k => m <= k)
    <==> n == 0 || m <= i && m <= i + (n - 1) * c

lemma {:rw} {:free} forall m: int, i: int, c: int, n: int ::
  invs(for ⌊counter(i, c, n)⌋ check k => k < m)
    <==> n == 0 || i < m && i + (n - 1) * c < m

// a counter by 1 or -1 avoids m if m lies outside of its range, e.g. for loops i != N
lemma {:rw} {:free} forall m: int, i: int, n: int ::
  invs(for ⌊counter(i, 1, n)⌋ check k => k != m)
    <==> m < i || i + n <= m

lemma {:rw} {:free} forall m: int, i: int, n: int ::
  invs(for ⌊counter(i, -1, n)⌋ check k => k != m)
    <==> i < m || m <= i - n

lemma <a> {:rw} {:free} forall x: a, xs: seq<a> ::
  invs(for xs check v => v == x)
    <==> xs == ⌊consts(length(xs), x)⌋

lemma <a> {:rw} {:free} forall b: bool, xs: seq<a> ::
  invs(for xs check v => b)
    <==> length(xs) == 0 || b

// current

lemma {:rw} {:free} forall i: int, c: int, n: int ::
  current(counter(i, c, n))
    == i + n * c

lemma <a> {:rw} {:free} forall x: a, y: a, i: int, c: int, n: int ::
  current(trace(x, for ⌊counter(i, c, n)⌋ do z, v => y))
    == if n == 0 then x else y

lemma <a> {:rw} {:free} forall n: int, x: a ::
  current(consts(n, x))
    == x

lemma <a> {:rw} {:free} forall a: array<a, int>, k: a, values: seq<int> ::
  current(trace(a, for values do b, v => b[k := b[k] + v]))
    == a[k := a[k] + sum(values)]

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  current(sums(x, values))
    == x + sum(values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  current(parities(x, values))
    == x + parity(values)

lemma {:rw} {:free} forall x: int, i: int, c: int, n: int ::
  current(maxs(x, ⌊counter(i, c, n)⌋))
    == if n == 0 then x else max(x, max(i, i + (n - 1) * c))

lemma {:rw} {:free} forall x: int, y: int, n: int ::
  current(maxs(x, ⌊consts(n, y)⌋))
    == if n == 0 then x else max(x, y)

lemma {:rw} {:free} forall x: int, i: int, c: int, n: int ::
  current(mins(x, ⌊counter(i, c, n)⌋))
    == if n == 0 then x else min(x, min(i, i + (n - 1) * c))

lemma {:rw} {:free} forall x: int, y: int, n: int ::
  current(mins(x, ⌊consts(n, y)⌋))
    == if n == 0 then x else min(x, y)

// the minima are the negated maxima of the negated values,
// not a rewrite rule, which would replace mins by maxs everywhere
lemma {:free} forall x: int, values: seq<int> ::
  current(mins(x, values))
    == -current(maxs(-x, maps(for values yield v => -v)))

lemma <a> {:rw} {:free} forall x: int, e: a, vs: seq<a> ::
  current(counts(x, e, vs))
    == x + count(e, vs)

// steps

lemma {:rw} {:free} forall i: int, c: int, n: int ::
  steps(counter(i, c, n))
    == n

lemma <a> {:rw} {:free} forall n: int, x: a ::
  steps(consts(n, x))
    == n

lemma <a, b> {:rw} {:free} forall a: array<a, b>, keys: seq<a>, values: seq<b> ::
  steps(stores(a, keys, values))
    == length(keys)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  steps(sums(x, values))
    == length(values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  steps(maxs(x, values))
    == length(values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  steps(mins(x, values))
    == length(values)

lemma <a> {:rw} {:free} forall x: int, e: a, vs: seq<a> ::
  steps(counts(x, e, vs))
    == length(vs)

// length

// all but the last element of a trace have the number of its steps
lemma {:rw} {:free} forall X: Trace<int> ::
  length(⌊X⌋)
    == steps(X)

lemma <a> {:rw} {:free} forall k: int, xs: seq<a> ::
  if 0 <= k <= length(xs)
  then length(prefix(k, xs))
         == k

lemma <a, b> {:rw} {:free} forall a: array<a, b>, keys: seq<a> ::
  length(selects(a, keys))
    == length(keys)

// earlier

lemma {:rw} {:free} forall k: int, i: int, c: int, n: int ::
  earlier(k, ⌊counter(i, c, n)⌋)
    == i + k * c

lemma <a> {:rw} {:free} forall x: a, xs: seq<a> ::
  earlier(indexof(x, xs), xs)
    == x

lemma <a> {:rw} {:free} forall k: int, n: int, x: a ::
  earlier(k, ⌊consts(n, x)⌋)
    == x

lemma <a, b> {:rw} {:free} forall j: int, a: array<a, b>, keys: seq<a> ::
  earlier(j, selects(a, keys))
    == a[earlier(j, keys)]

lemma {:rw} {:free} forall j: int, x: int, values: seq<int> ::
  earlier(j, ⌊sums(x, values)⌋)
    == x + sum(prefix(j, values))

lemma <a> {:rw} {:free} forall j: int, x: int, e: a, vs: seq<a> ::
  earlier(j, ⌊counts(x, e, vs)⌋)
    == x + count(e, prefix(j, vs))

lemma <a> {:rw} {:free} forall j: int, k: int, xs: seq<a> ::
  earlier(j, prefix(k, xs))
    == earlier(j, xs)

// prefix

lemma {:rw} {:free} forall k: int, i: int, c: int, n: int ::
  if 0 <= k <= n
  then prefix(k, ⌊counter(i, c, n)⌋)
         == ⌊counter(i, c, k)⌋

lemma <a> {:rw} {:free} forall k: int, n: int, x: a ::
  if 0 <= k <= n
  then prefix(k, ⌊consts(n, x)⌋)
         == ⌊consts(k, x)⌋

lemma <a, b> {:rw} {:free} forall k: int, a: array<a, b>, keys: seq<a> ::
  if 0 <= k <= length(keys)
  then prefix(k, selects(a, keys))
         == selects(a, prefix(k, keys))

lemma <a, b> {:rw} {:free} forall k: int, a: array<a, b>, keys: seq<a>, values: seq<b> ::
  if 0 <= k <= length(keys)
  then prefix(k, ⌊stores(a, keys, values)⌋)
         == ⌊stores(a, prefix(k, keys), prefix(k, values))⌋

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k <= length(values)
  then prefix(k, ⌊sums(x, values)⌋)
         == ⌊sums(x, prefix(k, values))⌋

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k <= length(values)
  then prefix(k, ⌊maxs(x, values)⌋)
         == ⌊maxs(x, prefix(k, values))⌋

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k <= length(values)
  then prefix(k, ⌊mins(x, values)⌋)
         == ⌊mins(x, prefix(k, values))⌋

lemma <a> {:rw} {:free} forall k: int, x: int, e: a, vs: seq<a> ::
  if 0 <= k <= length(vs)
  then prefix(k, ⌊counts(x, e, vs)⌋)
         == ⌊counts(x, e, prefix(k, vs))⌋

lemma <a> {:rw} {:free} forall xs: seq<a> ::
  prefix(0, xs)
    == []

lemma <a> {:rw} {:free} forall xs: seq<a> ::
  prefix(length(xs), xs)
    == xs

lemma <a> {:rw} {:free} forall j: int, k: int, xs: seq<a> ::
  if 0 <= j <= k <= length(xs)
  then prefix(j, prefix(k, xs))
         == prefix(j, xs)

// occurs

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  occurs(j, ⌊counter(i, 1, n)⌋)
    <==> i <= j < i + n

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  occurs(j, ⌊counter(i, -1, n)⌋)
    <==> i - n < j <= i

lemma <a> {:rw} {:free} forall x: a, n: int, y: a ::
  occurs(x, ⌊consts(n, y)⌋)
    <==> n != 0 && x == y

lemma <a> {:free} forall x: a, k: int, xs: seq<a> ::
  if 0 <= k <= length(xs) && occurs(x, prefix(k, xs))
  then occurs(x, xs)

// indexof

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  if i <= j < i + n
  then indexof(j, ⌊counter(i, 1, n)⌋)
         == j - i

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  if i - n < j <= i
  then indexof(j, ⌊counter(i, -1, n)⌋)
         == i - j

// distincts

lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if c != 0
  then distincts(⌊counter(i, c, n)⌋)

lemma <a> {:free} forall k: int, xs: seq<a> ::
  if 0 <= k <= length(xs) && distincts(xs)
  then distincts(prefix(k, xs))

// selects

lemma <a, b> {:rw} {:free} forall a: array<a, b>, keys: seq<a>, values: seq<b> ::
  if distincts(keys)
  then selects(current(stores(a, keys, values)), keys)
         == values

lemma {:rw} {:free} forall a: array<int, int>, n: int, i: int, d: int ::
  if 0 <= d
  then selects(current(shifts(a, ⌊counter(i, 1, n)⌋, d)), ⌊counter(i, 1, n)⌋)
         == selects(a, ⌊counter(i + d, 1, n)⌋)

// array selects

lemma <a, b> {:rw} {:free} forall k: a, a: array<a, b>, keys: seq<a>, values: seq<b> ::
  current(stores(a, keys, values))[k]
    == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]

// not a rewrite rule, since it loops: the index k may be rewritten to earlier(j, ...) by the assumptions,
// instead, the two lemmas below distinguish whether k occurs among the first j keys
lemma <a, b> {:free} forall k: a, j: int, a: array<a, b>, keys: seq<a>, values: seq<b> ::
  earlier(j, ⌊stores(a, keys, values)⌋)[k]
    == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]

// Note, indexof(k, prefix(j, keys)) <= indexof(k, keys) but not equal, since indexof is the *last* occurrence
lemma <a, b> {:rw} {:free} forall k: a, j: int, a: array<a, b>, keys: seq<a>, values: seq<b> ::
  if occurs(k, prefix(j, keys))
  then earlier(j, ⌊stores(a, keys, values)⌋)[k]
         == earlier(indexof(k, prefix(j, keys)), values)

lemma <a, b> {:rw} {:free} forall k: a, j: int, a: array<a, b>, keys: seq<a>, values: seq<b> ::
  if !occurs(k, prefix(j, keys))
  then earlier(j, ⌊stores(a, keys, values)⌋)[k]
         == a[k]

lemma {:rw} {:free} forall a: array<int, int>, n: int, i: int, d: int, k: int ::
  if 0 <= d
  then current(shifts(a, ⌊counter(i, 1, n)⌋, d))[k]
         == if i <= k < i + n then a[k + d] else a[k]

// sum, which is linear, and the linear transformations are moved to the outside

lemma {:rw} {:free}
  sum([])
    == 0

lemma {:rw} {:free} forall n: int, x: int ::
  sum(⌊consts(n, x)⌋)
    == x * n

lemma {:rw} {:free} forall values: seq<int> ::
  sum(maps(for values yield v => -v))
    == -sum(values)

lemma {:rw} {:free} forall values: seq<int>, a: int ::
  sum(maps(for values yield v => a * v))
    == a * sum(values)

lemma {:rw} {:free} forall xs: seq<int>, ys: seq<int> ::
  sum(maps(for xs, ys yield v, w => v + w))
    == sum(xs) + sum(ys)

// the arithmetic series, which is exact, since n * (n - 1) is even
lemma {:rw} {:free} forall i: int, c: int, n: int ::
  sum(⌊counter(i, c, n)⌋)
    == (2 * i + (n - 1) * c) * n / 2

lemma <a> {:rw} {:free} forall a: array<a, int>, k: a, v: int, keys: seq<a> ::
  if distincts(keys)
  then sum(selects(a[k := v], keys))
         == if occurs(k, keys) then sum(selects(a, keys)) + v - a[k] else sum(selects(a, keys))

// parity

lemma <a> {:rw} {:free} forall a: array<a, int>, k: a, v: int, keys: seq<a> ::
  if distincts(keys)
  then parity(selects(a[k := v], keys))
         == if occurs(k, keys)
            then parity(selects(a, keys)) + (if v % 2 == 0 then 1 else -1) - (if a[k] % 2 == 0 then 1 else -1)
            else parity(selects(a, keys))

// count

lemma <a> {:rw} {:free} forall n: int, e: a, v: a ::
  count(e, ⌊consts(n, v)⌋)
    == if v == e then n else 0

// an update of a visited key replaces its contribution, as for sum and parity
lemma <a, b> {:rw} {:free} forall a: array<a, b>, k: a, w: b, e: b, keys: seq<a> ::
  if distincts(keys)
  then count(e, selects(a[k := w], keys))
         == if occurs(k, keys)
            then count(e, selects(a, keys)) + (if w == e then 1 else 0) - (if a[k] == e then 1 else 0)
            else count(e, selects(a, keys))

// the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body
lemma {:rw} {:free} forall m: int, i: int, n: int ::
  if i <= m <= i + n
  then count(true, maps(for ⌊counter(i, 1, n)⌋ yield k => k < m))
         == m - i

lemma {:rw} {:free} forall m: int, i: int, n: int ::
  if i <= m <= i + n
  then count(false, maps(for ⌊counter(i, 1, n)⌋ yield k => k < m))
         == i + n - m

lemma {:rw} {:free} forall m: int, i: int, n: int ::
  if i <= m <= i + n
  then count(true, maps(for ⌊counter(i, 1, n)⌋ yield k => m <= k))
         == i + n - m

lemma {:rw} {:free} forall m: int, i: int, n: int ::
  if i <= m <= i + n
  then count(false, maps(for ⌊counter(i, 1, n)⌋ yield k => m <= k))
         == m - i

lemma <a> {:rw} {:free} forall e: a, vs: seq<a> ::
  0 <= count(e, vs)

lemma <a> {:rw} {:free} forall e: a, vs: seq<a> ::
  count(e, vs) <= length(vs)

// bounds

// the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
lemma {:rw} {:free} forall x: int, values: seq<int> ::
  x <= current(maxs(x, values))

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  earlier(k, values) <= current(maxs(x, values))

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  current(mins(x, values)) <= x

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  current(mins(x, values)) <= earlier(k, values)
