// aggregation: sums, parities, counts, maxima and minima as folds of the multiset of the values (the multisets of the
// core, cvc5's bags), since none of them depends on the order, and the prefix traces of a list that compute them, with
// their acceleration (current, earlier); linearity of sums, indicators, and bounds; permutations of arrays (a swap, a
// rotation) as lemmas on the multisets of their values, such that an aggregate of a permuted array is the same term as
// that of the original; compactions and filters (stores at counted positions); an optional module over teq.dfy
// (-include teq:aggregation); a constant sequence of a dependency is ⌊consts(n, c)⌋ (consts_choice of teq.dfy), whose
// sum is sum_consts; the bounds of counts and of the prefix maxima and minima by their initial value are forward lemmas

// the multiset of the elements of a list, the counterpart of Dafny's multiset(s) for the lists of the database (a
// datatype, not seq); two lists have the same one exactly if one is a permutation of the other
function {:rw} {:teq} elems<a>(xs: List<a>): multiset<a>
{
  match xs
  case nil => multiset{}
  case cons(y, ys) => multiset{y} + elems(ys)
}

// the aggregates of a multiset; without body, since a multiset has no structural recursion, and characterized by the
// lemmas on the operations of multisets below; the count of a value is its multiplicity m[e] of the core
// the sum
function {:teq} sum(m: multiset<int>): int

// the parity, the number of even minus the number of odd elements
function {:teq} parity(m: multiset<int>): int

// the maximum and the minimum of x and the elements
function {:teq} max(x: int, m: multiset<int>): int

function {:teq} min(x: int, m: multiset<int>): int

// the aggregates of the operations on multisets, always towards the arithmetic of the integers; the difference of the
// core cuts off at zero (cvc5's bag.difference_subtract), hence only of a submultiset; the maximum and the minimum not
// over a difference, since they have no inverse
// (unused on SV-COMP; the empty sum, kept as a law of sum)
lemma {:rw} {:teq} sum_empty()
  ensures sum(multiset{}) == 0

lemma {:rw} {:teq} sum_single(x: int)
  ensures sum(multiset{x}) == x

lemma {:rw} {:teq} sum_union(m: multiset<int>, n: multiset<int>)
  ensures sum(m + n) == sum(m) + sum(n)

lemma {:rw} {:teq} sum_difference(m: multiset<int>, n: multiset<int>)
  requires n <= m
  ensures sum(m - n) == sum(m) - sum(n)

lemma {:rw} {:teq} parity_empty()
  ensures parity(multiset{}) == 0

lemma {:rw} {:teq} parity_single(x: int)
  ensures parity(multiset{x}) == if { case x % 2 == 0 => 1 case x % 2 != 0 => -1 }

lemma {:rw} {:teq} parity_union(m: multiset<int>, n: multiset<int>)
  ensures parity(m + n) == parity(m) + parity(n)

lemma {:rw} {:teq} parity_difference(m: multiset<int>, n: multiset<int>)
  requires n <= m
  ensures parity(m - n) == parity(m) - parity(n)

lemma {:rw} {:teq} multiplicity_empty<a>(e: a)
  ensures (multiset{} as multiset<a>)[e] == 0

lemma {:rw} {:teq} multiplicity_single<a>(v: a, e: a)
  ensures multiset{v}[e] == if { case v == e => 1 case v != e => 0 }

lemma {:rw} {:teq} multiplicity_union<a>(m: multiset<a>, n: multiset<a>, e: a)
  ensures (m + n)[e] == m[e] + n[e]

lemma {:rw} {:teq} multiplicity_difference<a>(m: multiset<a>, n: multiset<a>, e: a)
  requires n <= m
  ensures (m - n)[e] == m[e] - n[e]

lemma {:rw} {:teq} max_empty(x: int)
  ensures max(x, multiset{}) == x

lemma {:rw} {:teq} max_single(x: int, v: int)
  ensures max(x, multiset{v}) == if { case x <= v => v case v < x => x }

lemma {:rw} {:teq} max_union(x: int, m: multiset<int>, n: multiset<int>)
  ensures max(x, m + n) == max(max(x, m), n)

lemma {:rw} {:teq} min_empty(x: int)
  ensures min(x, multiset{}) == x

lemma {:rw} {:teq} min_single(x: int, v: int)
  ensures min(x, multiset{v}) == if { case x <= v => x case v < x => v }

lemma {:rw} {:teq} min_union(x: int, m: multiset<int>, n: multiset<int>)
  ensures min(x, m + n) == min(min(x, m), n)

// a value read at a position of a list is among its values
lemma {:rw} {:teq} single_earlier_le_elems<a>(j: int, xs: List<a>)
  requires 0 <= j < length(xs)
  ensures (multiset{earlier(j, xs)} <= elems(xs)) <==> true

// a value read at one of the keys is among the values read there
lemma {:rw} {:teq} single_select_le_elems(a: array<int, int>, k: int, keys: List<int>)
  requires occurs(k, keys)
  ensures (multiset{a[k]} <= elems(selects(a, keys))) <==> true

// sums: the fold comes after the counter lemmas of teq.dfy, since a counter is a trace of sums of ones as well

function {:teq} {:fold} sums(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do s, v :: s + v)
}

lemma {:rw} {:teq} length_sums(x: int, values: List<int>)
  ensures length(⌊sums(x, values)⌋) == length(values)

lemma {:rw} {:teq} current_sums(x: int, values: List<int>)
  ensures current(sums(x, values))
    == x + sum(elems(values))

lemma {:rw} {:teq} earlier_sums(j: int, x: int, values: List<int>)
  ensures earlier(j, ⌊sums(x, values)⌋)
    == x + sum(elems(prefix(j, values)))

// (unused on SV-COMP; the prefix of the fold sums, kept as such)
lemma {:rw} {:teq} prefix_sums(k: int, x: int, values: List<int>)
  ensures prefix(k, ⌊sums(x, values)⌋)
    == ⌊sums(x, prefix(k, values))⌋

lemma {:rw} {:teq} sum_consts(n: int, x: int)
  requires 0 <= n
  ensures sum(elems(⌊consts(n, x)⌋))
    == x * n

lemma {:rw} {:teq} sum_counter(i: int, c: int, n: int)
  requires 0 <= n
  ensures sum(elems(⌊counter(i, c, n)⌋))
    == (2 * i + (n - 1) * c) * n / 2

// the prefix maxima and minima starting with an initial value
// (used on SV-COMP by standard_maxInArray_ground only)
function {:teq} {:fold} maxs(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case m < v => v case v <= m => m)
}

lemma {:rw} {:teq} length_maxs(x: int, values: List<int>)
  ensures length(⌊maxs(x, values)⌋) == length(values)

lemma {:rw} {:teq} current_maxs(x: int, values: List<int>)
  ensures current(maxs(x, values))
    == max(x, elems(values))

lemma {:rw} {:teq} earlier_maxs(j: int, x: int, values: List<int>)
  ensures earlier(j, ⌊maxs(x, values)⌋)
    == max(x, elems(prefix(j, values)))

lemma {:rw} {:teq} prefix_maxs(k: int, x: int, values: List<int>)
  ensures prefix(k, ⌊maxs(x, values)⌋)
    == ⌊maxs(x, prefix(k, values))⌋

// (used on SV-COMP by standard_minInArray_ground-2 only)
function {:teq} {:fold} mins(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case v < m => v case m <= v => m)
}

lemma {:rw} {:teq} length_mins(x: int, values: List<int>)
  ensures length(⌊mins(x, values)⌋) == length(values)

lemma {:rw} {:teq} current_mins(x: int, values: List<int>)
  ensures current(mins(x, values))
    == min(x, elems(values))

lemma {:rw} {:teq} earlier_mins(j: int, x: int, values: List<int>)
  ensures earlier(j, ⌊mins(x, values)⌋)
    == min(x, elems(prefix(j, values)))

lemma {:rw} {:teq} prefix_mins(k: int, x: int, values: List<int>)
  ensures prefix(k, ⌊mins(x, values)⌋)
    == ⌊mins(x, prefix(k, values))⌋

// the number of occurrences of a value, counted from an initial value
// (used on SV-COMP by half, sumt2 only)
function {:teq} {:fold} counts<a>(x: int, e: a, vs: List<a>): Trace<int>
{
  trace(x, for vs do y, v :: case v == e => y + 1 case v != e => y)
}

lemma {:rw} {:teq} length_counts<a>(x: int, e: a, vs: List<a>)
  ensures length(⌊counts(x, e, vs)⌋) == length(vs)

// on booleans, the guards are the values themselves; the occurrences of false come first,
// since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
lemma {:rw} {:teq} counts_false(x: int, bs: List<bool>)
  ensures trace(x, for bs do y, b :: case !b => y + 1 case b => y)
    == counts(x, false, bs)

// (used on SV-COMP by mono-crafted_10 only)
lemma {:rw} {:teq} counts_true(x: int, bs: List<bool>)
  ensures trace(x, for bs do y, b :: case b => y + 1 case !b => y)
    == counts(x, true, bs)

// a value that adds a in the iterations where C holds and keeps its value otherwise, x0 plus a times the number of
// those iterations
// (from loops-crafted-1: mono-crafted_12)
lemma {:rw} {:teq} current_trace_step_or_keep(x0: int, n: int, a: int, xs: List<int>, C: (int) -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, xs do z, k, x :: case C(x) => z + a case !C(x) => z))
    == x0 + a * elems(maps(for xs yield x :: C(x)))[true]

lemma {:rw} {:teq} current_trace_add_at<a>(a: array<a, int>, k: a, values: List<int>)
  ensures current(trace(a, for values do b, v :: b[k := b[k] + v]))
    == a[k := a[k] + sum(elems(values))]

// a histogram: the increments at the keys a[k] add to each cell v the number of occurrences of v among the keys
// (from examples/dafny/algorithms/counting_sort.dfy; unused on SV-COMP)
lemma {:rw} {:teq} current_trace_histogram(c0: array<int, int>, a: array<int, int>, n: int, hs: List<int>, v: int)
  ensures current(trace(c0, for ⌊counter(0, 1, n)⌋, hs do c, k, h :: c[a[k] := c[a[k]] + 1]))[v]
    == c0[v] + elems(selects(a, ⌊counter(0, 1, n)⌋))[v]

lemma {:rw} {:teq} current_counts<a>(x: int, e: a, vs: List<a>)
  ensures current(counts(x, e, vs))
    == x + elems(vs)[e]

lemma {:rw} {:teq} earlier_counts<a>(j: int, x: int, e: a, vs: List<a>)
  ensures earlier(j, ⌊counts(x, e, vs)⌋)
    == x + elems(prefix(j, vs))[e]

lemma {:rw} {:teq} prefix_counts<a>(k: int, x: int, e: a, vs: List<a>)
  ensures prefix(k, ⌊counts(x, e, vs)⌋)
    == ⌊counts(x, e, prefix(k, vs))⌋

// the aggregates of the values read at distinct keys after a store: the stored value replaces the old one if the key is
// among them, otherwise nothing changes; one per aggregate with an inverse (sum, parity, count), restored from the
// legacy database of 0.50.3 (distincts of a counter is distincts_counter of teq.dfy)
// (for array-patterns: the store of the last iteration of a loop before its break)
lemma {:rw} {:teq} sum_selects_update<a>(a: array<a, int>, k: a, v: int, keys: List<a>)
  requires distincts(keys)
  ensures sum(elems(selects(a[k := v], keys)))
    == if {
      case occurs(k, keys) => sum(elems(selects(a, keys))) + v - a[k]
      case !occurs(k, keys) => sum(elems(selects(a, keys)))
    }

lemma {:rw} {:teq} parity_selects_update<a>(a: array<a, int>, k: a, v: int, keys: List<a>)
  requires distincts(keys)
  ensures parity(elems(selects(a[k := v], keys)))
    == if {
      case occurs(k, keys) =>
        parity(elems(selects(a, keys))) + if { case v % 2 == 0 => 1 case v % 2 != 0 => -1 }
          - if { case a[k] % 2 == 0 => 1 case a[k] % 2 != 0 => -1 }
      case !occurs(k, keys) => parity(elems(selects(a, keys)))
    }

lemma {:rw} {:teq} count_selects_update<a, b>(a: array<a, b>, k: a, w: b, e: b, keys: List<a>)
  requires distincts(keys)
  ensures elems(selects(a[k := w], keys))[e]
    == if {
      case occurs(k, keys) =>
        elems(selects(a, keys))[e] + if { case w == e => 1 case w != e => 0 }
          - if { case a[k] == e => 1 case a[k] != e => 0 }
      case !occurs(k, keys) => elems(selects(a, keys))[e]
    }

// the prefix sums of n copies of c, from x, are the counter from x by c: the counter of an inner loop, whose trace is
// folded into sums over its dependency before that is known to be a counter (see examples/dafny/sorting/nested_sum.dfy)
lemma {:rw} {:teq} sums_consts(x: int, n: int, c: int)
  ensures sums(x, ⌊consts(n, c)⌋)
    == counter(x, c, n)

// a sum of the values over a counter of n iterations is at least, or at most, e if each value times n is, whatever the
// cases of the values (they are decided case by case in the condition, see Simplify.atom), e.g. 0 < sum of positive
// values; at least needs an iteration, since the empty sum 0 satisfies the condition vacuously; the left-hand sides
// are comparisons, whose constants bind e; the values may read further dependencies hs, e.g. the choices of a loop
// (from loop-invgen/large_const, MonoCera: brs2-brs5, ms2-ms5)
lemma {:rw} {:teq} sum_above(n: int, hs: List<int>, V: (int, int) -> int, e: int)
  requires 0 < n && invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: e <= n * V(k, h))
  ensures e <= sum(elems(maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: V(k, h))))

lemma {:rw} {:teq} sum_below(n: int, hs: List<int>, V: (int, int) -> int, e: int)
  requires 0 <= e && invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: n * V(k, h) <= e)
  ensures sum(elems(maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: V(k, h)))) <= e

// a sum of the remainders k % m of the iterations k from 0 is at most n (m - 1), which sum_below does not decide,
// since n * (k % m) is not linear
lemma {:rw} {:teq} sum_mod_below(n: int, m: int, e: int)
  requires 0 <= n && 0 < m && n * (m - 1) <= e
  ensures sum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: case 0 < k => k % m case k <= 0 => 0))) <= e

lemma {:rw} {:teq} sum_neg(values: List<int>)
  ensures sum(elems(maps(for values yield v :: -v)))
    == -sum(elems(values))

lemma {:rw} {:teq} sum_scale(values: List<int>, a: int)
  ensures sum(elems(maps(for values yield v :: a * v)))
    == a * sum(elems(values))

// after the negation and the scaling, since v + w also matches a single summand -e or a * e, with w = 0, whose sum
// contains the same sum again
lemma {:rw} {:teq} sum_add(xs: List<int>, ys: List<int>)
  ensures sum(elems(maps(for xs, ys yield v, w :: v + w)))
    == sum(elems(xs)) + sum(elems(ys))

// a sum of indicators, 1 where a condition holds and 0 otherwise, is the number of values where it holds, which the
// lemmas on counts evaluate
// (used on SV-COMP by brs1 only)
lemma {:rw} {:teq} sum_indicator_true<a>(xs: List<a>, P: a -> bool)
  ensures sum(elems(maps(for xs yield x :: case P(x) => 1 case !P(x) => 0)))
    == elems(maps(for xs yield x :: P(x)))[true]

// (unused on SV-COMP; the pair of sum_indicator_true)
lemma {:rw} {:teq} sum_indicator_false<a>(xs: List<a>, P: a -> bool)
  ensures sum(elems(maps(for xs yield x :: case P(x) => 0 case !P(x) => 1)))
    == elems(maps(for xs yield x :: P(x)))[false]

// (used on SV-COMP by nest-if3 only)
lemma {:rw} {:teq} count_consts<a>(n: int, e: a, v: a)
  requires 0 <= n
  ensures elems(⌊consts(n, v)⌋)[e]
    == if {
      case v == e => n
      case v != e => 0
    }

// the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body; the counts of
// false are the others, by count_false_true below
// (used on SV-COMP by gj2007, mono-crafted_1, mono-crafted_9 only)
lemma {:rw} {:teq} count_true_below(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))[true]
    == m - i

// (used on SV-COMP by brs1, mono-crafted_10 only)
lemma {:rw} {:teq} count_true_above(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))[true]
    == i + n - m

lemma {:fw} {:teq} count_nonnegative<a>(e: a, vs: List<a>)
  ensures 0 <= elems(vs)[e]

// the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
// (from half, sumt2, the only tasks of SV-COMP that use it)
lemma {:rw} {:teq} count_remainder(n: int, m: int, r: int)
  requires 0 <= n && 0 < m && 0 <= r < m
  ensures elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: k % m))[r] == (n + m - 1 - r) / m

// among the truth values of a map over the n iterations, those that are false are the others than those that are
// true; the dependencies are kept as matched, such that the counts are syntactically equal to those of the program
// (from sumt2)
lemma {:rw} {:teq} count_false_true(i: int, c: int, n: int, hs: List<int>, P: (int, int) -> bool)
  requires 0 <= n
  ensures elems(maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))[false]
    == n - elems(maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))[true]

// the iterations where a value is r are counted by the occurrences of r among the values
// (from sumt2, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} count_true_eq(ks: List<int>, r: int, hs: List<int>, F: (int, int) -> int)
  ensures elems(maps(for ks, hs yield k, h :: F(k, h) == r))[true]
    == elems(maps(for ks, hs yield k, h :: F(k, h)))[r]

// the initial value is a bound of the maxima and minima, which are attained by some value otherwise
// (used on SV-COMP by standard_maxInArray_ground only)
lemma {:fw} {:teq} max_initial(x: int, values: List<int>)
  ensures x <= max(x, elems(values))

// (used on SV-COMP by standard_maxInArray_ground only)
lemma {:rw} {:teq} max_earlier(k: int, x: int, values: List<int>)
  ensures earlier(k, values) <= max(x, elems(values))

// the values of a loop are a prefix of the list it reads (maps_earlier), whose reads within the prefix are bounded
// alike, since a read of the list is no read of the prefix
// (from standard_maxInArray_ground)
lemma {:rw} {:teq} max_prefix_earlier(k: int, x: int, n: int, xs: List<int>)
  requires 0 <= k < n
  ensures earlier(k, xs) <= max(x, elems(prefix(n, xs)))

// (used on SV-COMP by standard_minInArray_ground-2 only)
lemma {:fw} {:teq} min_initial(x: int, values: List<int>)
  ensures min(x, elems(values)) <= x

// (used on SV-COMP by standard_minInArray_ground-2 only)
lemma {:rw} {:teq} min_earlier(k: int, x: int, values: List<int>)
  ensures min(x, elems(values)) <= earlier(k, values)

// (from standard_minInArray_ground-2)
lemma {:rw} {:teq} min_prefix_earlier(k: int, x: int, n: int, xs: List<int>)
  requires 0 <= k < n
  ensures min(x, elems(prefix(n, xs))) <= earlier(k, xs)

// the maximum seeded with the read at h and continued with the reads at i, ..., i + n - 1, for h = i - 1, bounds the
// reads at h, ..., i + n - 1, e.g. largest = a[0] before a loop from 1
// (from sanfoundry_27_ground, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} max_seeded_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures earlier(j, xs) <= max(earlier(h, xs), elems(maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs))))

// (unused on SV-COMP; the counterpart of max_seeded_earlier)
lemma {:rw} {:teq} min_seeded_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures min(earlier(h, xs), elems(maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs)))) <= earlier(j, xs)

// permutations: a swap of two positions among distinct keys preserves the multiset of the values read there; the values
// are conditions, since the simplifier evaluates the reads of the swap before the lemma matches
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

// compactions and filters: a store at a position j that counts the iterations where a guard holds, C[j++] = i or
// bb[b++] = aa[a]; the folds keep the keys as a list, a variable ⌊K⌋ of the program, and the counts are variables of the
// conditions, matched against the facts, since the arithmetic compares terms with binders literally, not modulo the
// names of their bound variables, and does not identify ⌊K⌋ with ⌊counter(0, 1, n)⌋ below a binder (TODO.md)

// the iterations k where P(k) holds stored at the positions 0, 1, ... in the order of the loop
// (from standard_partial_init_ground)
function {:teq} {:fold} compacts(c0: array<int, int>, ks: List<int>, P: (int) -> bool): Trace<array<int, int>>
{
  trace(c0, for ks, ⌊counts(0, true, maps(for ks yield k :: P(k)))⌋ do c, k, j :: case P(k) => c[j := k] case !P(k) => c)
}

lemma {:rw} {:teq} length_compacts(c0: array<int, int>, ks: List<int>, P: (int) -> bool)
  ensures length(⌊compacts(c0, ks, P)⌋) == length(ks)

// the x-th of them is at least x, and at most x plus the iterations without P after it
// (from standard_partial_init_ground)
lemma {:rw} {:teq} select_current_compacts_lower(c0: array<int, int>, K: Trace<int>, n: int, m: int, x: int,
                                                 P: (int) -> bool)
  requires K == counter(0, 1, n)
  requires m == elems(maps(for ⌊K⌋ yield k :: P(k)))[true]
  requires 0 <= x < m
  ensures x <= current(compacts(c0, ⌊K⌋, P))[x]

// (from standard_partial_init_ground)
lemma {:rw} {:teq} select_current_compacts_upper(c0: array<int, int>, K: Trace<int>, n: int, m: int, x: int,
                                                 P: (int) -> bool)
  requires K == counter(0, 1, n)
  requires m == elems(maps(for ⌊K⌋ yield k :: P(k)))[true]
  requires 0 <= x < m
  ensures current(compacts(c0, ⌊K⌋, P))[x] + m <= x + n

// the values F(k) of the iterations where b <= F(k) holds stored at the positions 0, 1, ..., hence the first m
// positions, for the count m, hold values not below b
// (from standard_partition_ground-2, standard_partition_original_ground)
function {:teq} {:fold} filters_above(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int): Trace<array<int, int>>
{
  trace(c0, for ks, ⌊counts(0, true, maps(for ks yield k :: b <= F(k)))⌋ do c, k, j ::
        case b <= F(k) => c[j := F(k)] case F(k) < b => c)
}

lemma {:rw} {:teq} length_filters_above(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int)
  ensures length(⌊filters_above(c0, ks, b, F)⌋) == length(ks)

// (from standard_partition_ground-2, standard_partition_original_ground)
lemma {:rw} {:teq} select_current_filters_above(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int, m: int,
                                                x: int)
  requires m == elems(maps(for ks yield k :: b <= F(k)))[true]
  requires 0 <= x < m
  ensures b <= current(filters_above(c0, ks, b, F))[x]

// the same for the values below b, e.g. in the else branch, whose count is the iterations minus the count of the
// others, as counts_false states it
// (from standard_partition_original_ground)
function {:teq} {:fold} filters_below(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int): Trace<array<int, int>>
{
  trace(c0, for ks, ⌊counts(0, false, maps(for ks yield k :: b <= F(k)))⌋ do c, k, j ::
        case b <= F(k) => c case F(k) < b => c[j := F(k)])
}

lemma {:rw} {:teq} length_filters_below(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int)
  ensures length(⌊filters_below(c0, ks, b, F)⌋) == length(ks)

// (from standard_partition_original_ground)
lemma {:rw} {:teq} select_current_filters_below(c0: array<int, int>, K: Trace<int>, n: int, b: int, F: (int) -> int,
                                                m: int, x: int)
  requires K == counter(0, 1, n)
  requires elems(maps(for ⌊K⌋ yield k :: b <= F(k)))[true] + m == n
  requires 0 <= x < m
  ensures current(filters_below(c0, ⌊K⌋, b, F))[x] < b

// the prefix parities starting with an initial value
// (unused on SV-COMP, with its current_parities; kept as a fold of the module)
function {:teq} {:fold} parities(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do s, v :: case v % 2 == 0 => s + 1 case v % 2 != 0 => s - 1)
}

lemma {:rw} {:teq} length_parities(x: int, values: List<int>)
  ensures length(⌊parities(x, values)⌋) == length(values)

// (unused on SV-COMP; the final value of the fold parities)
lemma {:rw} {:teq} current_parities(x: int, values: List<int>)
  ensures current(parities(x, values))
    == x + parity(elems(values))

lemma {:rw} {:teq} earlier_parities(j: int, x: int, values: List<int>)
  ensures earlier(j, ⌊parities(x, values)⌋)
    == x + parity(elems(prefix(j, values)))

lemma {:rw} {:teq} prefix_parities(k: int, x: int, values: List<int>)
  ensures prefix(k, ⌊parities(x, values)⌋)
    == ⌊parities(x, prefix(k, values))⌋

// the recurrences of arrays whose values are sums (from arrays.dfy of the per-variable form)
// the same for a sum kept in the cell j of an array, e.g. sum[0] of a one-element array in C: only the cell j is
// written, hence it is read from the final array
// (from MonoCera: brs1-brs5, ms2-ms5)
lemma {:rw} {:teq} select_current_trace_reset_add(a0: array<int, int>, j: int, n: int, c: int, G: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case k == 0 => a[j := c] case 0 < k => a[j := a[j] + G(k)]))[j]
      == if {
        case n <= 0 => a0[j]
        case 0 < n => c + sum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: case 0 < k => G(k) case k <= 0 => 0)))
      }

// the same where the addition is split by a guard P, whose other case adds 0 and keeps the array, the form that the
// conditional of the value takes once lifted into cases (Simplify.choices, since 0.52.7), e.g. sum[0] + (i % 2 == 0 ?
// 2 : 0); the sum is bounded by sum_below
// (from MonoCera: brs2-brs5)
lemma {:rw} {:teq} select_current_trace_reset_add_keep(a0: array<int, int>, j: int, n: int, c: int, P: (int) -> bool,
    G: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  case k == 0 => a[j := c] case 0 < k && P(k) => a[j := a[j] + G(k)] case 0 < k && !P(k) => a))[j]
      == if {
        case n <= 0 => a0[j]
        case 0 < n =>
          c + sum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: case 0 < k && P(k) => G(k) case k <= 0 || !P(k) => 0)))
      }

// the same for a sum kept in a scalar, whose summand of the read of a map with cases is lifted into the cases of the
// update (Simplify.choices)
// (from examples/dafny/teq/sum_cases.dfy)
lemma {:rw} {:teq} current_trace_reset_add_keep(x0: int, n: int, c: int, P: (int) -> bool, G: (int) -> int)
  ensures
    current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k ::
                  case k == 0 => c case 0 < k && P(k) => x + G(k) case 0 < k && !P(k) => x))
      == if {
        case n <= 0 => x0
        case 0 < n =>
          c + sum(elems(maps(for ⌊counter(0, 1, n)⌋ yield k :: case 0 < k && P(k) => G(k) case k <= 0 || !P(k) => 0)))
      }

// an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
// of the predecessor, is the initial element plus the sum of G over the positions before
// (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
lemma {:rw} {:teq} select_current_trace_prefix_sums(b0: array<int, int>, n: int, j: int, G: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := G(k) + b[k]]))[j]
    == if {
      case 0 <= j <= n => b0[0] + sum(elems(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k))))
      case !(0 <= j <= n) => b0[j]
    }

// the same with two added terms, since a higher-order summand matches a single summand only (see TODO.md)
// (from nsqm, nsqmf, pcomp, pcompf, sqm; unused on SV-COMP, whose tasks nsqm, pcomp remain open for other reasons)
lemma {:rw} {:teq} select_current_trace_prefix_sums_add(b0: array<int, int>, n: int, j: int, G: (int) -> int,
                                                 H: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := b[k] + G(k) + H(k)]))[j]
    == if {
      case 0 <= j <= n => b0[0] + sum(elems(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k) + H(k))))
      case !(0 <= j <= n) => b0[j]
    }

// a recurrence in an array: the first cell set to c, each further cell i the previous one plus G(i), so the cell j is
// c plus the sum of G over 1, ..., j, e.g. a[i] = a[i - 1] + 2 and b[i] = b[i - 1] + a[i - 1] of ifeqn1 (needs the
// read a[i - 1] matched as a[k + -1], see Rewrite.summands)
// (from ifeqn1, ifeqn2)
lemma {:rw} {:teq} select_current_trace_recurrence(a0: array<int, int>, n: int, c: int, j: int, G: (int) -> int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, i ::
            case i == 0 => a[0 := c] case 0 < i => a[i := a[i - 1] + G(i)]))[j]
    == if {
      case 0 <= j && j < n => c + sum(elems(maps(for ⌊counter(1, 1, j)⌋ yield k :: G(k))))
      case !(0 <= j && j < n) => a0[j]
    }
