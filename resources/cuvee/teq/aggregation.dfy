// aggregation: sums, parities, maxima, minima, and counts as traces and as functions of lists, with their acceleration
// (current, earlier, prefix), linearity, indicators, and bounds; the abstractions of iteration constraints over values
// (consts_prefix, below_prefix, nonneg_prefix) extracted from teq.dfy on Oct 11, 2026 as one of the modules that -teq
// injects in the order of TEQ.modules, teq.dfy itself is kept but not injected; this file assumes the core declarations
// of teq.dfy (Nat, integer, natural, List, length, unspecified, Trace, current, butlast, counter, earlier, prefix,
// occurs, indexof, distincts, consts), counters.dfy, and arrays.dfy (selects); the attributes and the order of the
// lemmas are those of teq.dfy

// the first n values of js are all c
function {:teq} consts_prefix(n: Nat, c: int, js: List<int>): bool
{
  match n
  case zero => true
  case succ(m) => consts_prefix(m, c, js) && earlier(m, js) == c
}

// the first n values of xs are at most b, and nonnegative, for the values chosen in each of n iterations; the lemmas
// that abstract the iteration constraints by them are local to the tasks (see linear-inequality-inv-a), since they
// would match the bound of every loop, e.g. x < N as x + 1 <= N, and hide it from the lemmas on traces
function {:teq} below_prefix(n: Nat, xs: List<int>, b: int): bool
{
  match n
  case zero => true
  case succ(m) => below_prefix(m, xs, b) && earlier(m, xs) <= b
}

// the first n values of xs are nonnegative
function {:teq} nonneg_prefix(n: Nat, xs: List<int>): bool
{
  match n
  case zero => true
  case succ(m) => nonneg_prefix(m, xs) && 0 <= earlier(m, xs)
}

// the prefix sums of a sequence starting with an initial value
function {:teq} {:fold} sums(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do s, v :: s + v)
}

// the prefix parities starting with an initial value
function {:teq} {:fold} parities(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do s, v :: case v % 2 == 0 => s + 1 case v % 2 != 0 => s - 1)
}

// the prefix maxima and minima starting with an initial value
function {:teq} {:fold} maxs(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case m < v => v case v <= m => m)
}

function {:teq} {:fold} mins(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case v < m => v case m <= v => m)
}

// the number of occurrences of a value, counted from an initial value
function {:teq} {:fold} counts<a>(x: int, e: a, vs: List<a>): Trace<int>
{
  trace(x, for vs do y, v :: case v == e => y + 1 case v != e => y)
}

// on booleans, the guards are the values themselves; the occurrences of false come first,
// since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
lemma {:rw} {:teq} counts_false_def(x: int, bs: List<bool>)
  ensures trace(x, for bs do y, b :: case !b => y + 1 case b => y)
    == counts(x, false, bs)

lemma {:rw} {:teq} counts_true_def(x: int, bs: List<bool>)
  ensures trace(x, for bs do y, b :: case b => y + 1 case !b => y)
    == counts(x, true, bs)

// the values of a sequence at the iterations 0, ..., n - 1 are all c, e.g. the final values of an inner counter
// (from nested_sum)
lemma {:rw} {:teq} consts_prefix_def(n: Nat, c: int, js: List<int>, hs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(natural(k), js) == c) <==> consts_prefix(n, c, js)

lemma {:rw} {:teq} current_trace_add_at<a>(a: array<a, int>, k: a, values: List<int>)
  ensures current(trace(a, for values do b, v :: b[k := b[k] + v]))
    == a[k := a[k] + sum(values)]

lemma {:rw} {:teq} current_sums(x: int, values: List<int>)
  ensures current(sums(x, values))
    == x + sum(values)

lemma {:rw} {:teq} current_parities(x: int, values: List<int>)
  ensures current(parities(x, values))
    == x + parity(values)

lemma {:rw} {:teq} current_maxs_counter(x: int, i: int, c: int, n: Nat)
  ensures current(maxs(x, ⌊counter(i, c, n)⌋))
    == if n == zero then x else max(x, max(i, i + (integer(n) - 1) * c))

lemma {:rw} {:teq} current_maxs_consts(x: int, y: int, n: Nat)
  ensures current(maxs(x, ⌊consts(n, y)⌋))
    == if n == zero then x else max(x, y)

lemma {:rw} {:teq} current_mins_counter(x: int, i: int, c: int, n: Nat)
  ensures current(mins(x, ⌊counter(i, c, n)⌋))
    == if n == zero then x else min(x, min(i, i + (integer(n) - 1) * c))

lemma {:rw} {:teq} current_mins_consts(x: int, y: int, n: Nat)
  ensures current(mins(x, ⌊consts(n, y)⌋))
    == if n == zero then x else min(x, y)

lemma {:rw} {:teq} current_counts<a>(x: int, e: a, vs: List<a>)
  ensures current(counts(x, e, vs))
    == x + count(e, vs)

lemma {:rw} {:teq} earlier_sums(j: Nat, x: int, values: List<int>)
  ensures earlier(j, ⌊sums(x, values)⌋)
    == x + sum(prefix(j, values))

lemma {:rw} {:teq} earlier_counts<a>(j: Nat, x: int, e: a, vs: List<a>)
  ensures earlier(j, ⌊counts(x, e, vs)⌋)
    == x + count(e, prefix(j, vs))

lemma {:rw} {:teq} prefix_sums(k: Nat, x: int, values: List<int>)
  ensures prefix(k, ⌊sums(x, values)⌋)
    == ⌊sums(x, prefix(k, values))⌋

lemma {:rw} {:teq} prefix_maxs(k: Nat, x: int, values: List<int>)
  ensures prefix(k, ⌊maxs(x, values)⌋)
    == ⌊maxs(x, prefix(k, values))⌋

lemma {:rw} {:teq} prefix_mins(k: Nat, x: int, values: List<int>)
  ensures prefix(k, ⌊mins(x, values)⌋)
    == ⌊mins(x, prefix(k, values))⌋

lemma {:rw} {:teq} prefix_counts<a>(k: Nat, x: int, e: a, vs: List<a>)
  ensures prefix(k, ⌊counts(x, e, vs)⌋)
    == ⌊counts(x, e, prefix(k, vs))⌋

// the prefix sums of n copies of c, from x, are the counter from x by c: the counter of an inner loop, whose trace is
// folded into sums over its dependency before that is known to be a counter (see examples/dafny/sorting/nested_sum.dfy)
lemma {:rw} {:teq} sums_consts(x: int, n: Nat, c: int)
  ensures sums(x, ⌊consts(n, c)⌋)
    == counter(x, c, n)

lemma {:rw} {:teq} sum_empty()
  ensures sum(nil)
    == 0

lemma {:rw} {:teq} sum_consts(n: Nat, x: int)
  ensures sum(⌊consts(n, x)⌋)
    == x * integer(n)

// the sum of the first n values of a sequence that are all c, e.g. the final values of the counter of an inner loop;
// the iteration constraint is abstracted by consts_prefix (see consts_prefix_def), since an iteration constraint as
// a side condition does not terminate
// (from examples/dafny/algorithms/nested_sum.dfy)
lemma {:rw} {:teq} sum_consts_prefix(n: Nat, c: int, js: List<int>)
  requires consts_prefix(n, c, js)
  ensures sum(js)
    == c * integer(n)

// the sum of n values that are at most b is at most n * b, that of nonnegative ones is nonnegative and at least each
// of them; the left-hand sides are comparisons
// (from linear-inequality-inv-a, -b, -c, -d)
lemma {:rw} {:teq} sum_below_prefix(n: Nat, xs: List<int>, b: int, c: int)
  requires below_prefix(n, xs, b) && integer(n) * b <= c
  ensures sum(xs) <= c

lemma {:rw} {:teq} earlier_nonneg_prefix(n: Nat, xs: List<int>, j: Nat)
  requires nonneg_prefix(n, xs) && integer(j) < integer(n)
  ensures earlier(j, xs) <= sum(xs)

lemma {:rw} {:teq} sum_nonneg_prefix(n: Nat, xs: List<int>)
  requires nonneg_prefix(n, xs)
  ensures 0 <= sum(xs)

// a sum of n terms that are each 0, c, or d is at most n times the largest of them, and one of remainders k % m of
// the iterations k from 0 at most n (m - 1); the left-hand sides are comparisons, whose constants bind the bound,
// unlike sum_below_prefix, whose bound occurs only in its side condition
// (from MonoCera: brs2-brs5, ms2-ms5)
lemma {:rw} {:teq} sum_cases_below(n: Nat, c: int, d: int, e: int, P: (int) -> bool)
  requires 0 <= e && integer(n) * c <= e && integer(n) * d <= e
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then (if P(k) then c else d) else 0)) <= e

lemma {:rw} {:teq} sum_mod_below(n: Nat, m: int, e: int)
  requires 0 < m && integer(n) * (m - 1) <= e
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then k % m else 0)) <= e

lemma {:rw} {:teq} sum_neg(values: List<int>)
  ensures sum(maps(for values yield v :: -v))
    == -sum(values)

lemma {:rw} {:teq} sum_scale(values: List<int>, a: int)
  ensures sum(maps(for values yield v :: a * v))
    == a * sum(values)

lemma {:rw} {:teq} sum_add(xs: List<int>, ys: List<int>)
  ensures sum(maps(for xs, ys yield v, w :: v + w))
    == sum(xs) + sum(ys)

// the arithmetic series, which is exact, since n * (n - 1) is even
lemma {:rw} {:teq} sum_counter(i: int, c: int, n: Nat)
  ensures sum(⌊counter(i, c, n)⌋)
    == (2 * i + (integer(n) - 1) * c) * integer(n) / 2

// a sum of indicators, 1 where a condition holds and 0 otherwise, is the number of values where it holds, which the
// lemmas on counts evaluate; for one dependency and for two, as in loops with a choice
lemma {:rw} {:teq} sum_indicator_true<a>(xs: List<a>, P: a -> bool)
  ensures sum(maps(for xs yield x :: if P(x) then 1 else 0)) == count(true, maps(for xs yield x :: P(x)))

lemma {:rw} {:teq} sum_indicator_false<a>(xs: List<a>, P: a -> bool)
  ensures sum(maps(for xs yield x :: if P(x) then 0 else 1)) == count(false, maps(for xs yield x :: P(x)))

lemma {:rw} {:teq} sum_indicator_true_2<a, b>(xs: List<a>, ys: List<b>, P: (a, b) -> bool)
  ensures sum(maps(for xs, ys yield x, y :: if P(x, y) then 1 else 0)) == count(true, maps(for xs, ys yield x, y :: P(x, y)))

lemma {:rw} {:teq} sum_indicator_false_2<a, b>(xs: List<a>, ys: List<b>, P: (a, b) -> bool)
  ensures sum(maps(for xs, ys yield x, y :: if P(x, y) then 0 else 1)) == count(false, maps(for xs, ys yield x, y :: P(x, y)))

lemma {:rw} {:teq} sum_selects_update<a>(a: array<a, int>, k: a, v: int, keys: List<a>)
  requires distincts(keys)
  ensures sum(selects(a[k := v], keys))
    == if occurs(k, keys) then sum(selects(a, keys)) + v - a[k] else sum(selects(a, keys))

lemma {:rw} {:teq} parity_selects_update<a>(a: array<a, int>, k: a, v: int, keys: List<a>)
  requires distincts(keys)
  ensures parity(selects(a[k := v], keys))
    == if occurs(k, keys)
       then parity(selects(a, keys)) + (if v % 2 == 0 then 1 else -1) - (if a[k] % 2 == 0 then 1 else -1)
       else parity(selects(a, keys))

lemma {:rw} {:teq} count_consts<a>(n: Nat, e: a, v: a)
  ensures count(e, ⌊consts(n, v)⌋)
    == if v == e then integer(n) else 0

// an update of a visited key replaces its contribution, as for sum and parity
lemma {:rw} {:teq} count_selects_update<a, b>(a: array<a, b>, k: a, w: b, e: b, keys: List<a>)
  requires distincts(keys)
  ensures count(e, selects(a[k := w], keys))
    == if occurs(k, keys)
       then count(e, selects(a, keys)) + (if w == e then 1 else 0) - (if a[k] == e then 1 else 0)
       else count(e, selects(a, keys))

// the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body
lemma {:rw} {:teq} count_true_below(m: int, i: int, n: Nat)
  requires i <= m <= i + integer(n)
  ensures count(true, maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))
    == m - i

lemma {:rw} {:teq} count_false_below(m: int, i: int, n: Nat)
  requires i <= m <= i + integer(n)
  ensures count(false, maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))
    == i + integer(n) - m

lemma {:rw} {:teq} count_true_above(m: int, i: int, n: Nat)
  requires i <= m <= i + integer(n)
  ensures count(true, maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))
    == i + integer(n) - m

lemma {:rw} {:teq} count_false_above(m: int, i: int, n: Nat)
  requires i <= m <= i + integer(n)
  ensures count(false, maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))
    == m - i

lemma {:rw} {:teq} count_nonnegative<a>(e: a, vs: List<a>)
  ensures 0 <= count(e, vs)

// the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
// (from half, sumt2)
lemma {:rw} {:teq} count_remainder(n: Nat, m: int, r: int, hs: List<int>)
  requires 0 < m && 0 <= r < m
  ensures count(r, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: k % m)) == (integer(n) + m - 1 - r) / m

// among the truth values of a map over the n iterations, those that are false are the others than those that are
// true; the dependencies are kept as matched, such that the counts are syntactically equal to those of the program
// (from sumt2)
lemma {:rw} {:teq} count_false_true(i: int, c: int, n: Nat, hs: List<int>, P: (int, int) -> bool)
  ensures count(false, maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))
    == integer(n) - count(true, maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))

// the iterations where a value is r are counted by the occurrences of r among the values
// (from sumt2)
lemma {:rw} {:teq} count_true_eq(ks: List<int>, r: int, hs: List<int>, F: (int, int) -> int)
  ensures count(true, maps(for ks, hs yield k, h :: F(k, h) == r))
    == count(r, maps(for ks, hs yield k, h :: F(k, h)))

// the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
lemma {:rw} {:teq} current_maxs_initial(x: int, values: List<int>)
  ensures x <= current(maxs(x, values))

lemma {:rw} {:teq} current_maxs_earlier(k: Nat, x: int, values: List<int>)
  ensures earlier(k, values) <= current(maxs(x, values))

lemma {:rw} {:teq} current_mins_initial(x: int, values: List<int>)
  ensures current(mins(x, values)) <= x

lemma {:rw} {:teq} current_mins_earlier(k: Nat, x: int, values: List<int>)
  ensures current(mins(x, values)) <= earlier(k, values)

// the differences (k + 1)^3 - k^3 - 1 = 3 * k + 3 * k * k telescope to n^3 - n; teq.dfy splits such a sum by linearity
// first, hence the sum of 3 * k * k as the rest, such that the division atoms cancel
// (from pcomp, pcompf)
lemma {:rw} {:teq} sum_squares(n: Nat)
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: 3 * k * k))
    == integer(n) * integer(n) * integer(n) - integer(n) - 3 * ((-integer(n) + integer(n) * integer(n)) / 2)
