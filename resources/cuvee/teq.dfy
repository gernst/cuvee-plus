// the lemma database of -teq, which is injected at the beginning of its output:
// the functions on traces (see cuvee.core.Fun.trace), where butlast is written ⌊X⌋,
// and lemmas about them, which are rewrite rules of the simplifier ({:rw}) and assumed by the solvers ({:free})

// counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
// the last element of a trace
function current<a₀>(x₀: Trace<a₀>): a₀
// the number of steps of a trace, which is one less than the number of its elements
function steps<a₀>(x₀: Trace<a₀>): int
// the length of a sequence
function length<a₀>(x₀: seq<a₀>): int
// the elements of traces and sequences
function nth<a₀>(x₀: int, x₁: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
lemma {:rw} {:free} forall i: int, c: int, K: Trace<int> ::
  trace(i, for ⌊K⌋ do x, k => x + c) == counter(i, c, steps(K))

// the last element and the number of steps of a counter
lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if 0 <= n then current(counter(i, c, n)) == i + n * c

lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if 0 <= n then steps(counter(i, c, n)) == n

// all but the last element of a trace have the number of its steps
lemma {:rw} {:free} forall X: Trace<int> ::
  length(⌊X⌋) == steps(X)

// =====================================================================================================================
// LEMMAS THAT NEED TO BE CHECKED MANUALLY
//
// taken from the lemma database teq.bpl of the Boogie implementation of trace equation systems,
// assumed without proof ({:free}), where
//   counter(n) and range(i, c, n) of teq.bpl are counter(0, 1, n) and counter(i, c, n),
//   the preconditions on the bounds such as 0 <= n are added, on which teq.bpl relied implicitly,
//   the lemmas over counter(n) only that hold for arbitrary dependencies are generalized,
//   lemmas are instantiated at int and array<int,int>, since they cannot have type parameters,
//   the lemmas on select and store are omitted, which the simplifier applies itself (Simplify.select),
//   as well as those subsumed by the ones above (e.g. trace(i, for ⌊K⌋ do x, k => x + c)),
// and with the following corrections:
//   earlier(indexof(x, xs), xs) == x and the elements of selects, counter, and consts require that they exist,
//   map(for ⌊counter(0, 1, n)⌋ yield k => earlier(k, xs)) == xs requires that xs has length n,
//   the lemmas on sum and parity of selects(a[k := v], keys) require that the keys are distinct,
//   earlier(j, ⌊stores(a, keys, values)⌋)[k] is a[k] if k is not among the first j keys, not a[j]
// =====================================================================================================================

// the first k elements of a sequence
function prefix<a₀>(x₀: int, x₁: seq<a₀>): seq<a₀>

// whether x occurs in a sequence, and the index of its last occurrence (unspecified otherwise)
function occurs<a₀>(x₀: a₀, x₁: seq<a₀>): bool
function indexof<a₀>(x₀: a₀, x₁: seq<a₀>): int

// whether a sequence has no duplicates
function distincts<a₀>(x₀: seq<a₀>): bool

// consts(n, v) is the trace v, ..., v of n steps
function consts<a₀>(x₀: int, x₁: a₀): Trace<a₀>

// selects(a, keys) are the values of a at the keys,
// stores(a, keys, values) is the trace of the successive stores of the values at the keys into a
function selects<a₀, a₁>(x₀: array<a₀, a₁>, x₁: seq<a₀>): seq<a₁>
function stores<a₀, a₁>(x₀: array<a₀, a₁>, x₁: seq<a₀>, x₂: seq<a₁>): Trace<array<a₀, a₁>>

// shifts(a, keys, d) is the trace of the successive copies a[k] := a[k + d] for the keys
function shifts(x₀: array<int, int>, x₁: seq<int>, x₂: int): Trace<array<int, int>>

// the prefix sums of a sequence starting with an initial value, and the sum of a sequence
function sums(x₀: int, x₁: seq<int>): Trace<int>
function sum(x₀: seq<int>): int

// the prefix parities (the number of even minus the number of odd elements) starting with an initial value,
// and the parity of a sequence
function parities(x₀: int, x₁: seq<int>): Trace<int>
function parity(x₀: seq<int>): int

// the prefix maxima and minima starting with an initial value
function maxs(x₀: int, x₁: seq<int>): Trace<int>
function mins(x₀: int, x₁: seq<int>): Trace<int>

function max(m: int, n: int): int
{
  if m <= n then n else m
}

function min(m: int, n: int): int
{
  if m <= n then m else n
}

// the number of true values, counted from an initial value
function counts(x₀: int, x₁: seq<bool>): Trace<int>

// counters

lemma {:rw} {:free} forall n: int, xs: seq<int> ::
  if 0 <= n && length(xs) == n then map(for ⌊counter(0, 1, n)⌋ yield k => earlier(k, xs)) == xs

lemma {:rw} {:free} forall k: int, i: int, c: int, n: int ::
  if 0 <= k && k < n then earlier(k, ⌊counter(i, c, n)⌋) == i + k * c

lemma {:rw} {:free} forall k: int, i: int, c: int, n: int ::
  if 0 <= k && k <= n then prefix(k, ⌊counter(i, c, n)⌋) == ⌊counter(i, c, k)⌋

lemma {:rw} {:free} forall a: int, b: int, i: int, c: int, n: int ::
  if 0 <= n then map(for ⌊counter(i, c, n)⌋ yield v => a + b * v) == ⌊counter(a + b * i, b * c, n)⌋

lemma {:rw} {:free} forall m: int, i: int, c: int, n: int ::
  if 0 <= n then all(for ⌊counter(i, c, n)⌋ check k => m <= k) <==> n == 0 || m <= i && m <= i + (n - 1) * c

lemma {:rw} {:free} forall m: int, i: int, c: int, n: int ::
  if 0 <= n then all(for ⌊counter(i, c, n)⌋ check k => k < m) <==> n == 0 || i < m && i + (n - 1) * c < m

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  if 0 <= n then occurs(j, ⌊counter(i, 1, n)⌋) <==> i <= j && j < i + n

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  if 0 <= n then occurs(j, ⌊counter(i, -1, n)⌋) <==> i - n < j && j <= i

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  if i <= j && j < i + n then indexof(j, ⌊counter(i, 1, n)⌋) == j - i

lemma {:rw} {:free} forall j: int, i: int, n: int ::
  if i - n < j && j <= i then indexof(j, ⌊counter(i, -1, n)⌋) == i - j

lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if c != 0 then distincts(⌊counter(i, c, n)⌋)

// occurrences

lemma {:rw} {:free} forall x: int, xs: seq<int> ::
  if occurs(x, xs) then earlier(indexof(x, xs), xs) == x

// constants

lemma {:rw} {:free} forall x: int, xs: seq<int> ::
  trace(x, for xs do y, v => y) == consts(length(xs), x)

lemma {:rw} {:free} forall x: int, xs: seq<int> ::
  map(for xs yield v => x) == ⌊consts(length(xs), x)⌋

lemma {:rw} {:free} forall x: int, y: int, xs: seq<int> ::
  current(trace(x, for xs do z, v => y)) == if length(xs) == 0 then x else y

lemma {:rw} {:free} forall n: int, x: int ::
  if 0 <= n then current(consts(n, x)) == x

lemma {:rw} {:free} forall k: int, n: int, x: int ::
  if 0 <= k && k < n then earlier(k, ⌊consts(n, x)⌋) == x

lemma {:rw} {:free} forall x: int, xs: seq<int> ::
  all(for xs check v => v == x) <==> xs == ⌊consts(length(xs), x)⌋

lemma {:rw} {:free} forall x: int, n: int, y: int ::
  if 0 <= n then occurs(x, ⌊consts(n, y)⌋) <==> n != 0 && x == y

lemma {:rw} {:free} forall b: bool, xs: seq<int> ::
  all(for xs check v => b) <==> length(xs) == 0 || b

lemma {:rw} {:free} forall k: int, n: int, x: int ::
  if 0 <= k && k <= n then prefix(k, ⌊consts(n, x)⌋) == ⌊consts(k, x)⌋

// arrays

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int> ::
  map(for keys yield k => a[k]) == selects(a, keys)

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int>, values: seq<int> ::
  trace(a, for keys, values do b, k, v => b[k := v]) == stores(a, keys, values)

lemma {:rw} {:free} forall j: int, a: array<int, int>, keys: seq<int> ::
  if 0 <= j && j < length(keys) then earlier(j, selects(a, keys)) == a[earlier(j, keys)]

lemma {:rw} {:free} forall k: int, a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if length(keys) == length(values)
  then current(stores(a, keys, values))[k] == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]

// not a rewrite rule, since it loops: the index k may be rewritten to earlier(j, ...) by the assumptions,
// instead, the two lemmas below distinguish whether k occurs among the first j keys
lemma {:free} forall k: int, j: int, a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if 0 <= j && j < length(keys) && length(keys) == length(values)
  then earlier(j, ⌊stores(a, keys, values)⌋)[k]
         == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]

// Note, indexof(k, prefix(j, keys)) <= indexof(k, keys) but not equal, since indexof is the *last* occurrence
lemma {:rw} {:free} forall k: int, j: int, a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if 0 <= j && j < length(keys) && length(keys) == length(values) && occurs(k, prefix(j, keys))
  then earlier(j, ⌊stores(a, keys, values)⌋)[k] == earlier(indexof(k, prefix(j, keys)), values)

lemma {:rw} {:free} forall k: int, j: int, a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if 0 <= j && j < length(keys) && length(keys) == length(values) && !occurs(k, prefix(j, keys))
  then earlier(j, ⌊stores(a, keys, values)⌋)[k] == a[k]

// each key is visited once only if they are distinct, hence a[k] is still the initial value
lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int>, bs: seq<int>, cs: seq<int> ::
  if distincts(keys)
  then trace(a, for keys, bs, cs do b, k, x, y => b[k := x * b[k] + y])
         == trace(a, for keys, bs, cs do b, k, x, y => b[k := x * a[k] + y])

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if distincts(keys) && length(keys) == length(values) then selects(current(stores(a, keys, values)), keys) == values

lemma {:rw} {:free} forall k: int, a: array<int, int>, keys: seq<int> ::
  if 0 <= k && k <= length(keys) then prefix(k, selects(a, keys)) == selects(a, prefix(k, keys))

lemma {:rw} {:free} forall k: int, a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if 0 <= k && k <= length(keys) && length(keys) == length(values)
  then prefix(k, ⌊stores(a, keys, values)⌋) == ⌊stores(a, prefix(k, keys), prefix(k, values))⌋

// shifts, which are modeled for increasing keys and nonnegative offsets only, where the entries read are not yet modified

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int>, d: int ::
  trace(a, for keys do b, k => b[k := b[k + d]]) == shifts(a, keys, d)

lemma {:rw} {:free} forall a: array<int, int>, n: int, i: int, d: int, k: int ::
  if 0 <= n && 0 <= d
  then current(shifts(a, ⌊counter(i, 1, n)⌋, d))[k] == if i <= k && k < i + n then a[k + d] else a[k]

lemma {:rw} {:free} forall a: array<int, int>, n: int, i: int, d: int ::
  if 0 <= n && 0 <= d
  then selects(current(shifts(a, ⌊counter(i, 1, n)⌋, d)), ⌊counter(i, 1, n)⌋) == selects(a, ⌊counter(i + d, 1, n)⌋)

// sums, where sum is linear, and the linear transformations are moved to the outside

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do s, v => s + v) == sums(x, values)

lemma {:rw} {:free} forall a: array<int, int>, k: int, values: seq<int> ::
  current(trace(a, for values do b, v => b[k := b[k] + v])) == a[k := a[k] + sum(values)]

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  current(sums(x, values)) == x + sum(values)

lemma {:rw} {:free} forall j: int, x: int, values: seq<int> ::
  if 0 <= j && j < length(values) then earlier(j, ⌊sums(x, values)⌋) == x + sum(prefix(j, values))

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k && k <= length(values) then prefix(k, ⌊sums(x, values)⌋) == ⌊sums(x, prefix(k, values))⌋

lemma {:rw} {:free} forall n: int, x: int ::
  if 0 <= n then sum(⌊consts(n, x)⌋) == x * n

lemma {:rw} {:free} forall values: seq<int> ::
  sum(map(for values yield v => -v)) == -sum(values)

lemma {:rw} {:free} forall values: seq<int>, a: int ::
  sum(map(for values yield v => a * v)) == a * sum(values)

lemma {:rw} {:free} forall xs: seq<int>, ys: seq<int> ::
  sum(map(for xs, ys yield v, w => v + w)) == sum(xs) + sum(ys)

// the arithmetic series, which is exact, since n * (n - 1) is even
lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if 0 <= n then sum(⌊counter(i, c, n)⌋) == (2 * i + (n - 1) * c) * n / 2

lemma {:rw} {:free} forall a: array<int, int>, k: int, v: int, keys: seq<int> ::
  if distincts(keys)
  then sum(selects(a[k := v], keys)) == if occurs(k, keys) then sum(selects(a, keys)) + v - a[k] else sum(selects(a, keys))

// parities, which are linear like sums

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do s, v => if v % 2 == 0 then s + 1, if v % 2 != 0 then s - 1) == parities(x, values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  current(parities(x, values)) == x + parity(values)

lemma {:rw} {:free} forall a: array<int, int>, k: int, v: int, keys: seq<int> ::
  if distincts(keys)
  then parity(selects(a[k := v], keys))
         == if occurs(k, keys)
            then parity(selects(a, keys)) + (if v % 2 == 0 then 1 else -1) - (if a[k] % 2 == 0 then 1 else -1)
            else parity(selects(a, keys))

// maxima and minima

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do m, v => if m < v then v, if v <= m then m) == maxs(x, values)

lemma {:rw} {:free} forall x: int, i: int, c: int, n: int ::
  if 0 <= n then current(maxs(x, ⌊counter(i, c, n)⌋)) == if n == 0 then x else max(x, max(i, i + (n - 1) * c))

lemma {:rw} {:free} forall x: int, y: int, n: int ::
  if 0 <= n then current(maxs(x, ⌊consts(n, y)⌋)) == if n == 0 then x else max(x, y)

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k && k <= length(values) then prefix(k, ⌊maxs(x, values)⌋) == ⌊maxs(x, prefix(k, values))⌋

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  trace(x, for values do m, v => if m > v then v, if v >= m then m) == mins(x, values)

lemma {:rw} {:free} forall x: int, i: int, c: int, n: int ::
  if 0 <= n then current(mins(x, ⌊counter(i, c, n)⌋)) == if n == 0 then x else min(x, min(i, i + (n - 1) * c))

lemma {:rw} {:free} forall x: int, y: int, n: int ::
  if 0 <= n then current(mins(x, ⌊consts(n, y)⌋)) == if n == 0 then x else min(x, y)

lemma {:rw} {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k && k <= length(values) then prefix(k, ⌊mins(x, values)⌋) == ⌊mins(x, prefix(k, values))⌋

// a sum of the nonnegative values only does not decrease
lemma {:rw} {:free} forall x: int, values: seq<int> ::
  !(current(trace(x, for values do s, v => if 0 <= v then s + v, if v < 0 then s)) < x)

// counts

lemma {:rw} {:free} forall x: int, bs: seq<bool> ::
  trace(x, for bs do y, b => if b then y + 1, if !b then y) == counts(x, bs)

// =====================================================================================================================
// FURTHER LEMMAS THAT NEED TO BE CHECKED MANUALLY
//
// not from teq.bpl, which fit the approach: the elements and lengths of the functions above, which relate
// earlier and nth, the lengths of prefixes, and the facts that are needed for inductive invariants over prefixes
// =====================================================================================================================

// the number of true values of a sequence
function count(x₀: seq<bool>): int

// the elements of a trace and of all but its last element coincide
lemma {:rw} {:free} forall k: int, X: Trace<int> ::
  if 0 <= k && k < steps(X) then earlier(k, ⌊X⌋) == nth(k, X)

lemma {:free} forall X: Trace<int> ::
  current(X) == nth(steps(X), X)

// counters

lemma {:rw} {:free} forall k: int, i: int, c: int, n: int ::
  if 0 <= k && k <= n then nth(k, counter(i, c, n)) == i + k * c

// prefixes

lemma {:rw} {:free} forall k: int, xs: seq<int> ::
  if 0 <= k && k <= length(xs) then length(prefix(k, xs)) == k

lemma {:rw} {:free} forall xs: seq<int> ::
  prefix(length(xs), xs) == xs

lemma {:rw} {:free} forall j: int, k: int, xs: seq<int> ::
  if 0 <= j && j < k && k <= length(xs) then earlier(j, prefix(k, xs)) == earlier(j, xs)

lemma {:rw} {:free} forall j: int, k: int, xs: seq<int> ::
  if 0 <= j && j <= k && k <= length(xs) then prefix(j, prefix(k, xs)) == prefix(j, xs)

lemma {:free} forall x: int, k: int, xs: seq<int> ::
  if 0 <= k && k <= length(xs) && occurs(x, prefix(k, xs)) then occurs(x, xs)

lemma {:free} forall xs: seq<int> ::
  if distincts(xs) then forall k: int :: 0 <= k && k <= length(xs) ==> distincts(prefix(k, xs))

// the lengths and number of steps of the functions above

lemma {:rw} {:free} forall n: int, x: int ::
  if 0 <= n then steps(consts(n, x)) == n

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int> ::
  length(selects(a, keys)) == length(keys)

lemma {:rw} {:free} forall a: array<int, int>, keys: seq<int>, values: seq<int> ::
  if length(keys) == length(values) then steps(stores(a, keys, values)) == length(keys)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  steps(sums(x, values)) == length(values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  steps(maxs(x, values)) == length(values)

lemma {:rw} {:free} forall x: int, values: seq<int> ::
  steps(mins(x, values)) == length(values)

lemma {:rw} {:free} forall x: int, bs: seq<bool> ::
  steps(counts(x, bs)) == length(bs)

// the step of the prefix sums, for invariants of the form s == sum(prefix(i, values))
lemma {:free} forall k: int, values: seq<int> ::
  if 0 <= k && k < length(values) then sum(prefix(k + 1, values)) == sum(prefix(k, values)) + earlier(k, values)

lemma {:rw} {:free} forall values: seq<int> ::
  sum(prefix(0, values)) == 0

// the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
lemma {:free} forall x: int, values: seq<int> ::
  x <= current(maxs(x, values)) && current(mins(x, values)) <= x

lemma {:free} forall k: int, x: int, values: seq<int> ::
  if 0 <= k && k < length(values) then earlier(k, values) <= current(maxs(x, values)) && current(mins(x, values)) <= earlier(k, values)

// counts, which are linear like sums

lemma {:rw} {:free} forall x: int, bs: seq<bool> ::
  current(counts(x, bs)) == x + count(bs)

lemma {:free} forall bs: seq<bool> ::
  0 <= count(bs) && count(bs) <= length(bs)

lemma {:rw} {:free} forall k: int, x: int, bs: seq<bool> ::
  if 0 <= k && k <= length(bs) then prefix(k, ⌊counts(x, bs)⌋) == ⌊counts(x, prefix(k, bs))⌋

lemma {:rw} {:free} forall n: int, b: bool ::
  if 0 <= n then count(⌊consts(n, b)⌋) == if b then n else 0
