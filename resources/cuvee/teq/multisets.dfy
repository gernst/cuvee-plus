// multisets: the folds that do not depend on the order of a list as folds of its multiset (the multisets of the core,
// cvc5's bags), and the permutations of arrays (a swap, a rotation) as lemmas on the multisets of their values, such
// that a fold of a permuted array is the same term as that of the original; an optional module over teq.dfy
// (-include teq:multisets) after teq:aggregation, whose lemmas on lists apply first (doc/teq.md, "Multisets"); the lemmas
// are ordered from the simpler to the more specific ones

// the multiset of the elements of a list, the counterpart of Dafny's multiset(s) for the lists of the database (a
// datatype, not seq); two lists have the same one exactly if one is a permutation of the other
function {:rw} {:teq} elems<a>(xs: List<a>): multiset<a>
{
  match xs
  case nil => multiset{}
  case cons(y, ys) => multiset{y} + elems(ys)
}

// the folds of a multiset, for the folds of lists that do not depend on the order; without body, since a multiset has
// no structural recursion, and characterized by the lemmas below
function {:teq} msum(m: multiset<int>): int

function {:teq} mparity(m: multiset<int>): int

function {:teq} mmax(seed: int, m: multiset<int>): int

function {:teq} mmin(seed: int, m: multiset<int>): int

// the folds of the operations on multisets, always towards the arithmetic of the integers; the difference of the core
// cuts off at zero (cvc5's bag.difference_subtract), hence only of a submultiset
lemma {:rw} {:teq} msum_empty()
  ensures msum(multiset{}) == 0

lemma {:rw} {:teq} msum_single(x: int)
  ensures msum(multiset{x}) == x

lemma {:rw} {:teq} msum_union(m: multiset<int>, n: multiset<int>)
  ensures msum(m + n) == msum(m) + msum(n)

lemma {:rw} {:teq} msum_difference(m: multiset<int>, n: multiset<int>)
  requires n <= m
  ensures msum(m - n) == msum(m) - msum(n)

lemma {:rw} {:teq} mparity_empty()
  ensures mparity(multiset{}) == 0

lemma {:rw} {:teq} mparity_single(x: int)
  ensures mparity(multiset{x}) == if x % 2 == 0 then 1 else -1

lemma {:rw} {:teq} mparity_union(m: multiset<int>, n: multiset<int>)
  ensures mparity(m + n) == mparity(m) + mparity(n)

lemma {:rw} {:teq} mparity_difference(m: multiset<int>, n: multiset<int>)
  requires n <= m
  ensures mparity(m - n) == mparity(m) - mparity(n)

// the multiplicities of the operations on multisets (the count of a list is the multiplicity in its multiset, see
// count_elems); the difference of a submultiset subtracts
lemma {:rw} {:teq} multiplicity_empty<a>(e: a)
  ensures (multiset{} as multiset<a>)[e] == 0

lemma {:rw} {:teq} multiplicity_single<a>(v: a, e: a)
  ensures multiset{v}[e] == if v == e then 1 else 0

lemma {:rw} {:teq} multiplicity_union<a>(m: multiset<a>, n: multiset<a>, e: a)
  ensures (m + n)[e] == m[e] + n[e]

lemma {:rw} {:teq} multiplicity_difference<a>(m: multiset<a>, n: multiset<a>, e: a)
  requires n <= m
  ensures (m - n)[e] == m[e] - n[e]

// the maximum and the minimum from a seed, over the empty multiset, a single value and a union; not over a difference,
// since they have no inverse (max and min of teq:aggregation)
lemma {:rw} {:teq} mmax_empty(x: int)
  ensures mmax(x, multiset{}) == x

lemma {:rw} {:teq} mmax_single(x: int, v: int)
  ensures mmax(x, multiset{v}) == max(x, v)

lemma {:rw} {:teq} mmax_union(x: int, m: multiset<int>, n: multiset<int>)
  ensures mmax(x, m + n) == max(mmax(x, m), mmax(x, n))

lemma {:rw} {:teq} mmin_empty(x: int)
  ensures mmin(x, multiset{}) == x

lemma {:rw} {:teq} mmin_single(x: int, v: int)
  ensures mmin(x, multiset{v}) == min(x, v)

lemma {:rw} {:teq} mmin_union(x: int, m: multiset<int>, n: multiset<int>)
  ensures mmin(x, m + n) == min(mmin(x, m), mmin(x, n))

// the linearity of the sum of the multiset of a map, as that of the sum of a list (sum_neg, sum_scale, sum_add of
// teq:aggregation); the negation and the scaling before the addition, since v + w also matches a single summand
lemma {:rw} {:teq} msum_neg(values: List<int>)
  ensures msum(elems(maps(for values yield v :: -v)))
    == -msum(elems(values))

lemma {:rw} {:teq} msum_scale(values: List<int>, a: int)
  ensures msum(elems(maps(for values yield v :: a * v)))
    == a * msum(elems(values))

lemma {:rw} {:teq} msum_add(xs: List<int>, ys: List<int>)
  ensures msum(elems(maps(for xs, ys yield v, w :: v + w)))
    == msum(elems(xs)) + msum(elems(ys))

// a value read at a position of a list is among its values
lemma {:rw} {:teq} single_earlier_le_elems<a>(j: int, xs: List<a>)
  requires 0 <= j < length(xs)
  ensures (multiset{earlier(j, xs)} <= elems(xs)) <==> true

// a value read at one of the keys is among the values read there
lemma {:rw} {:teq} single_select_le_elems(a: array<int, int>, k: int, keys: List<int>)
  requires occurs(k, keys)
  ensures (multiset{a[k]} <= elems(selects(a, keys))) <==> true

// a fold of a list that does not depend on the order is the fold of its multiset, for all lists; the lemmas of
// teq:aggregation that consume a fold of a list have their twins on the fold of its multiset below, so that a
// conversion of an inner fold, which innermost rewriting applies first, preempts none of them
// (from reducercommutativity: sum, avg, sep, max)
lemma {:rw} {:teq} sum_elems(xs: List<int>)
  ensures sum(xs) == msum(elems(xs))

lemma {:rw} {:teq} parity_elems(xs: List<int>)
  ensures parity(xs) == mparity(elems(xs))

lemma {:rw} {:teq} count_elems<a>(e: a, xs: List<a>)
  ensures count(e, xs) == elems(xs)[e]

lemma {:rw} {:teq} current_maxs_elems(x: int, values: List<int>)
  ensures current(maxs(x, values)) == mmax(x, elems(values))

lemma {:rw} {:teq} current_mins_elems(x: int, values: List<int>)
  ensures current(mins(x, values)) == mmin(x, elems(values))

// the twins of the lemmas of teq:aggregation on folds of lists, the same statements on the folds of the multisets
// (sum_consts, sum_counter, ..., the updates, the bounds of the maxima and minima); not of its forward lemmas
lemma {:rw} {:teq} msum_consts(n: int, x: int)
  requires 0 <= n
  ensures msum(elems(⌊consts(n, x)⌋))
    == x * n

lemma {:rw} {:teq} msum_counter(i: int, c: int, n: int)
  requires 0 <= n
  ensures msum(elems(⌊counter(i, c, n)⌋))
    == (2 * i + (n - 1) * c) * n / 2

lemma {:rw} {:teq} msum_cases_below(n: int, c: int, d: int, e: int, P: (int) -> bool)
  requires 0 <= e && n * c <= e && n * d <= e
  ensures msum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then (if P(k) then c else d) else 0))) <= e

lemma {:rw} {:teq} msum_mod_below(n: int, m: int, e: int)
  requires 0 <= n && 0 < m && n * (m - 1) <= e
  ensures msum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then k % m else 0))) <= e

lemma {:rw} {:teq} msum_indicator_true<a>(xs: List<a>, P: a -> bool)
  ensures msum(elems(maps(for xs yield x :: if P(x) then 1 else 0))) == elems(maps(for xs yield x :: P(x)))[true]

lemma {:rw} {:teq} msum_indicator_false<a>(xs: List<a>, P: a -> bool)
  ensures msum(elems(maps(for xs yield x :: if P(x) then 0 else 1))) == elems(maps(for xs yield x :: P(x)))[false]

lemma {:rw} {:teq} msum_selects_update<a>(a: array<a, int>, k: a, v: int, keys: List<a>)
  requires distincts(keys)
  ensures msum(elems(selects(a[k := v], keys)))
    == if occurs(k, keys) then msum(elems(selects(a, keys))) + v - a[k] else msum(elems(selects(a, keys)))

lemma {:rw} {:teq} mparity_selects_update<a>(a: array<a, int>, k: a, v: int, keys: List<a>)
  requires distincts(keys)
  ensures mparity(elems(selects(a[k := v], keys)))
    == if occurs(k, keys)
       then mparity(elems(selects(a, keys))) + (if v % 2 == 0 then 1 else -1) - (if a[k] % 2 == 0 then 1 else -1)
       else mparity(elems(selects(a, keys)))

lemma {:rw} {:teq} mcount_selects_update<a, b>(a: array<a, b>, k: a, w: b, e: b, keys: List<a>)
  requires distincts(keys)
  ensures elems(selects(a[k := w], keys))[e]
    == if occurs(k, keys)
       then elems(selects(a, keys))[e] + (if w == e then 1 else 0) - (if a[k] == e then 1 else 0)
       else elems(selects(a, keys))[e]

lemma {:rw} {:teq} mcount_consts<a>(n: int, e: a, v: a)
  requires 0 <= n
  ensures elems(⌊consts(n, v)⌋)[e]
    == if v == e then n else 0

lemma {:rw} {:teq} mcount_true_below(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))[true]
    == m - i

lemma {:rw} {:teq} mcount_true_above(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))[true]
    == i + n - m

lemma {:rw} {:teq} mcount_remainder(n: int, m: int, r: int)
  requires 0 <= n && 0 < m && 0 <= r < m
  ensures elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: k % m))[r] == (n + m - 1 - r) / m

lemma {:rw} {:teq} mcount_false_true(i: int, c: int, n: int, hs: List<int>, P: (int, int) -> bool)
  requires 0 <= n
  ensures elems(maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))[false]
    == n - elems(maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))[true]

lemma {:rw} {:teq} mcount_true_eq(ks: List<int>, r: int, hs: List<int>, F: (int, int) -> int)
  ensures elems(maps(for ks, hs yield k, h :: F(k, h) == r))[true]
    == elems(maps(for ks, hs yield k, h :: F(k, h)))[r]

lemma {:rw} {:teq} mmax_earlier(k: int, x: int, values: List<int>)
  ensures earlier(k, values) <= mmax(x, elems(values))

lemma {:rw} {:teq} mmax_prefix_earlier(k: int, x: int, n: int, xs: List<int>)
  requires 0 <= k < n
  ensures earlier(k, xs) <= mmax(x, elems(prefix(n, xs)))

lemma {:rw} {:teq} mmin_earlier(k: int, x: int, values: List<int>)
  ensures mmin(x, elems(values)) <= earlier(k, values)

lemma {:rw} {:teq} mmin_prefix_earlier(k: int, x: int, n: int, xs: List<int>)
  requires 0 <= k < n
  ensures mmin(x, elems(prefix(n, xs))) <= earlier(k, xs)

lemma {:rw} {:teq} mmax_seeded_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures earlier(j, xs) <= mmax(earlier(h, xs), elems(maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs))))

lemma {:rw} {:teq} mmin_seeded_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures mmin(earlier(h, xs), elems(maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs)))) <= earlier(j, xs)

// a swap of two positions among distinct keys preserves the multiset of the values read there; the values are
// conditions, since the simplifier evaluates the reads of the swap before the lemma matches
// (from reducercommutativity, array-crafted bAnd, bor, xor)
lemma {:rw} {:teq} elems_selects_swap(a: array<int, int>, p: int, q: int, v: int, w: int, keys: List<int>)
  requires distincts(keys) && occurs(p, keys) && occurs(q, keys) && v == a[q] && w == a[p]
  ensures elems(selects(a[p := v][q := w], keys)) == elems(selects(a, keys))

// the shift of a loop that moves each element of i + 1, ..., i + n one position down: the values over i, ..., i + n
// lose the first and have the last twice, since the last position is not written; the rotation of a C program stores
// the old first element there afterwards, which the translation of the reads of its loops decomposes; the length of
// the keys m is a variable of its own, since n + 1 does not match a literal
// (from reducercommutativity, array-crafted bAnd, bor, xor)
lemma {:rw} {:teq} elems_selects_shift(a: array<int, int>, i: int, n: int, m: int)
  requires 0 <= n && m == n + 1
  ensures elems(selects(current(trace(a, for ⌊counter(i, 1, n)⌋ do x, k :: x[k := x[k + 1]])), ⌊counter(i, 1, m)⌋))
    == elems(selects(a, ⌊counter(i, 1, m)⌋)) - multiset{a[i]} + multiset{a[i + n]}

// a rotation by one over the positions i, ..., i + n: the shift, then the old first element stored at the end
// (from reducercommutativity, array-crafted bAnd, bor, xor)
lemma {:rw} {:teq} elems_selects_rotate(a: array<int, int>, i: int, n: int, m: int, v: int)
  requires 0 <= n && m == n + 1 && v == a[i]
  ensures elems(selects(current(trace(a, for ⌊counter(i, 1, n)⌋ do x, k :: x[k := x[k + 1]]))[i + n := v],
                        ⌊counter(i, 1, m)⌋))
    == elems(selects(a, ⌊counter(i, 1, m)⌋))
