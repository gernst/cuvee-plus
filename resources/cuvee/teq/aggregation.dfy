// aggregation: sums, parities, counts, maxima and minima as traces and as functions of lists, with their acceleration
// (current, earlier), linearity of sums, indicators, and bounds, compactions and filters (stores at counted positions);
// an optional module over teq.dfy (-include teq:aggregation); a constant sequence of a dependency is ⌊consts(n, c)⌋
// (consts_choice of teq.dfy), whose sum is sum_consts; the bounds of counts and of the prefix maxima and minima by
// their initial value are forward lemmas

// the functions of lists and integers that the aggregates fold
// the sum of a list
function {:rw} {:teq} sum(values: List<int>): int
{
  match values
  case nil => 0
  case cons(v, vs) => v + sum(vs)
}

// the parity of a list, the number of even minus the number of odd elements
function {:rw} {:teq} parity(values: List<int>): int
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
function {:rw} {:teq} count<a>(e: a, vs: List<a>): int
{
  match vs
  case nil => 0
  case cons(v, ws) => (if v == e then 1 else 0) + count(e, ws)
}

// sums: the fold comes after the counter lemmas of teq.dfy, since a counter is a trace of sums of ones as well

function {:teq} {:fold} sums(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do s, v :: s + v)
}

lemma {:rw} {:teq} length_sums(x: int, values: List<int>)
  ensures length(⌊sums(x, values)⌋) == length(values)

lemma {:rw} {:teq} current_sums(x: int, values: List<int>)
  ensures current(sums(x, values))
    == x + sum(values)

lemma {:rw} {:teq} earlier_sums(j: int, x: int, values: List<int>)
  ensures earlier(j, ⌊sums(x, values)⌋)
    == x + sum(prefix(j, values))

// (unused on SV-COMP; the prefix of the fold sums, kept as such)
lemma {:rw} {:teq} prefix_sums(k: int, x: int, values: List<int>)
  ensures prefix(k, ⌊sums(x, values)⌋)
    == ⌊sums(x, prefix(k, values))⌋

// (unused on SV-COMP; the empty sum, kept as a law of sum)
lemma {:rw} {:teq} sum_empty()
  ensures sum(nil)
    == 0

lemma {:rw} {:teq} sum_consts(n: int, x: int)
  requires 0 <= n
  ensures sum(⌊consts(n, x)⌋)
    == x * n

lemma {:rw} {:teq} sum_counter(i: int, c: int, n: int)
  requires 0 <= n
  ensures sum(⌊counter(i, c, n)⌋)
    == (2 * i + (n - 1) * c) * n / 2

// the prefix maxima and minima starting with an initial value
// (used on SV-COMP by standard_maxInArray_ground only)
function {:teq} {:fold} maxs(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case m < v => v case v <= m => m)
}

lemma {:rw} {:teq} length_maxs(x: int, values: List<int>)
  ensures length(⌊maxs(x, values)⌋) == length(values)

// (used on SV-COMP by standard_minInArray_ground-2 only)
function {:teq} {:fold} mins(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case v < m => v case m <= v => m)
}

lemma {:rw} {:teq} length_mins(x: int, values: List<int>)
  ensures length(⌊mins(x, values)⌋) == length(values)

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
    == x0 + a * count(true, maps(for xs yield x :: C(x)))

lemma {:rw} {:teq} current_trace_add_at<a>(a: array<a, int>, k: a, values: List<int>)
  ensures current(trace(a, for values do b, v :: b[k := b[k] + v]))
    == a[k := a[k] + sum(values)]

// a histogram: the increments at the keys a[k] add to each cell v the number of occurrences of v among the keys
// (from examples/dafny/algorithms/counting_sort.dfy; unused on SV-COMP)
lemma {:rw} {:teq} current_trace_histogram(c0: array<int, int>, a: array<int, int>, n: int, hs: List<int>, v: int)
  ensures current(trace(c0, for ⌊counter(0, 1, n)⌋, hs do c, k, h :: c[a[k] := c[a[k]] + 1]))[v]
    == c0[v] + count(v, selects(a, ⌊counter(0, 1, n)⌋))

lemma {:rw} {:teq} current_counts<a>(x: int, e: a, vs: List<a>)
  ensures current(counts(x, e, vs))
    == x + count(e, vs)

lemma {:rw} {:teq} earlier_counts<a>(j: int, x: int, e: a, vs: List<a>)
  ensures earlier(j, ⌊counts(x, e, vs)⌋)
    == x + count(e, prefix(j, vs))

// the aggregates of the values read at distinct keys after a store: the stored value replaces the old one if the key is
// among them, otherwise nothing changes; one per aggregate of lists (sum, parity, count), restored from the legacy
// database of 0.50.3 (distincts of a counter is distincts_counter of teq.dfy)
// (for array-patterns: the store of the last iteration of a loop before its break)
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

lemma {:rw} {:teq} count_selects_update<a, b>(a: array<a, b>, k: a, w: b, e: b, keys: List<a>)
  requires distincts(keys)
  ensures count(e, selects(a[k := w], keys))
    == if occurs(k, keys)
       then count(e, selects(a, keys)) + (if w == e then 1 else 0) - (if a[k] == e then 1 else 0)
       else count(e, selects(a, keys))

// the prefix sums of n copies of c, from x, are the counter from x by c: the counter of an inner loop, whose trace is
// folded into sums over its dependency before that is known to be a counter (see examples/dafny/sorting/nested_sum.dfy)
lemma {:rw} {:teq} sums_consts(x: int, n: int, c: int)
  ensures sums(x, ⌊consts(n, c)⌋)
    == counter(x, c, n)

// a sum of n terms that are each 0, c, or d is at most n times the largest of them, and one of remainders k % m of
// the iterations k from 0 at most n (m - 1); the left-hand sides are comparisons, whose constants bind the bound
// (from MonoCera: brs2-brs5, ms2-ms5)
lemma {:rw} {:teq} sum_cases_below(n: int, c: int, d: int, e: int, P: (int) -> bool)
  requires 0 <= e && n * c <= e && n * d <= e
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then (if P(k) then c else d) else 0)) <= e

lemma {:rw} {:teq} sum_mod_below(n: int, m: int, e: int)
  requires 0 <= n && 0 < m && n * (m - 1) <= e
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then k % m else 0)) <= e

lemma {:rw} {:teq} sum_neg(values: List<int>)
  ensures sum(maps(for values yield v :: -v))
    == -sum(values)

lemma {:rw} {:teq} sum_scale(values: List<int>, a: int)
  ensures sum(maps(for values yield v :: a * v))
    == a * sum(values)

// after the negation and the scaling, since v + w also matches a single summand -e or a * e, with w = 0, whose sum
// contains the same sum again
lemma {:rw} {:teq} sum_add(xs: List<int>, ys: List<int>)
  ensures sum(maps(for xs, ys yield v, w :: v + w))
    == sum(xs) + sum(ys)

// a sum of indicators, 1 where a condition holds and 0 otherwise, is the number of values where it holds, which the
// lemmas on counts evaluate
// (used on SV-COMP by brs1 only)
lemma {:rw} {:teq} sum_indicator_true<a>(xs: List<a>, P: a -> bool)
  ensures sum(maps(for xs yield x :: if P(x) then 1 else 0)) == count(true, maps(for xs yield x :: P(x)))

// (unused on SV-COMP; the pair of sum_indicator_true)
lemma {:rw} {:teq} sum_indicator_false<a>(xs: List<a>, P: a -> bool)
  ensures sum(maps(for xs yield x :: if P(x) then 0 else 1)) == count(false, maps(for xs yield x :: P(x)))

// (used on SV-COMP by nest-if3 only)
lemma {:rw} {:teq} count_consts<a>(n: int, e: a, v: a)
  requires 0 <= n
  ensures count(e, ⌊consts(n, v)⌋)
    == if v == e then n else 0

// the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body; the counts of
// false are the others, by count_false_true below
// (used on SV-COMP by gj2007, mono-crafted_1, mono-crafted_9 only)
lemma {:rw} {:teq} count_true_below(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures count(true, maps(for ⌊counter(i, 1, n)⌋ yield k :: k < m))
    == m - i

// (used on SV-COMP by brs1, mono-crafted_10 only)
lemma {:rw} {:teq} count_true_above(m: int, i: int, n: int)
  requires i <= m <= i + n
  ensures count(true, maps(for ⌊counter(i, 1, n)⌋ yield k :: m <= k))
    == i + n - m

lemma {:fw} {:teq} count_nonnegative<a>(e: a, vs: List<a>)
  ensures 0 <= count(e, vs)

// the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
// (from half, sumt2, the only tasks of SV-COMP that use it)
lemma {:rw} {:teq} count_remainder(n: int, m: int, r: int)
  requires 0 <= n && 0 < m && 0 <= r < m
  ensures count(r, maps(for ⌊counter(0, 1, n)⌋ yield k :: k % m)) == (n + m - 1 - r) / m

// among the truth values of a map over the n iterations, those that are false are the others than those that are
// true; the dependencies are kept as matched, such that the counts are syntactically equal to those of the program
// (from sumt2)
lemma {:rw} {:teq} count_false_true(i: int, c: int, n: int, hs: List<int>, P: (int, int) -> bool)
  requires 0 <= n
  ensures count(false, maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))
    == n - count(true, maps(for ⌊counter(i, c, n)⌋, hs yield k, h :: P(k, h)))

// the iterations where a value is r are counted by the occurrences of r among the values
// (from sumt2, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} count_true_eq(ks: List<int>, r: int, hs: List<int>, F: (int, int) -> int)
  ensures count(true, maps(for ks, hs yield k, h :: F(k, h) == r))
    == count(r, maps(for ks, hs yield k, h :: F(k, h)))

// the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
// (used on SV-COMP by standard_maxInArray_ground only)
lemma {:fw} {:teq} current_maxs_initial(x: int, values: List<int>)
  ensures x <= current(maxs(x, values))

// (used on SV-COMP by standard_maxInArray_ground only)
lemma {:rw} {:teq} current_maxs_earlier(k: int, x: int, values: List<int>)
  ensures earlier(k, values) <= current(maxs(x, values))

// the values of a loop are a prefix of the list it reads (maps_earlier), whose reads within the prefix are bounded
// alike, since a read of the list is no read of the prefix
// (from standard_maxInArray_ground)
lemma {:rw} {:teq} current_maxs_prefix_earlier(k: int, x: int, n: int, xs: List<int>)
  requires 0 <= k < n
  ensures earlier(k, xs) <= current(maxs(x, prefix(n, xs)))

// (used on SV-COMP by standard_minInArray_ground-2 only)
lemma {:fw} {:teq} current_mins_initial(x: int, values: List<int>)
  ensures current(mins(x, values)) <= x

// (used on SV-COMP by standard_minInArray_ground-2 only)
lemma {:rw} {:teq} current_mins_earlier(k: int, x: int, values: List<int>)
  ensures current(mins(x, values)) <= earlier(k, values)

// (from standard_minInArray_ground-2)
lemma {:rw} {:teq} current_mins_prefix_earlier(k: int, x: int, n: int, xs: List<int>)
  requires 0 <= k < n
  ensures current(mins(x, prefix(n, xs))) <= earlier(k, xs)

// the maximum seeded with the read at h and continued with the reads at i, ..., i + n - 1, for h = i - 1, bounds the
// reads at h, ..., i + n - 1, e.g. largest = a[0] before a loop from 1
// (from sanfoundry_27_ground, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} current_maxs_seeded_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures earlier(j, xs) <= current(maxs(earlier(h, xs), maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs))))

// (unused on SV-COMP; the counterpart of current_maxs_seeded_earlier)
lemma {:rw} {:teq} current_mins_seeded_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures current(mins(earlier(h, xs), maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs)))) <= earlier(j, xs)

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
  requires m == count(true, maps(for ⌊K⌋ yield k :: P(k)))
  requires 0 <= x < m
  ensures x <= current(compacts(c0, ⌊K⌋, P))[x]

// (from standard_partial_init_ground)
lemma {:rw} {:teq} select_current_compacts_upper(c0: array<int, int>, K: Trace<int>, n: int, m: int, x: int,
                                                 P: (int) -> bool)
  requires K == counter(0, 1, n)
  requires m == count(true, maps(for ⌊K⌋ yield k :: P(k)))
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
  requires m == count(true, maps(for ks yield k :: b <= F(k)))
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
  requires count(true, maps(for ⌊K⌋ yield k :: b <= F(k))) + m == n
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
    == x + parity(values)

// the recurrences of arrays whose values are sums (from arrays.dfy of the per-variable form)
// the same for a sum kept in the cell j of an array, e.g. sum[0] of a one-element array in C: only the cell j is
// written, hence it is read from the final array
// (from MonoCera: brs1-brs5, ms2-ms5)
lemma {:rw} {:teq} select_current_trace_reset_add(a0: array<int, int>, j: int, n: int, c: int, G: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case k == 0 => a[j := c] case 0 < k => a[j := a[j] + G(k)]))[j]
      == if n <= 0 then a0[j] else c + sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then G(k) else 0))

// the same where the addition is split by a guard P, whose other case adds 0 and keeps the array, the form that the
// conditional of the value takes once lifted into cases (Simplify.choices, since 0.52.7), e.g. sum[0] + (i % 2 == 0 ?
// 2 : 0); the sum is that of sum_cases_below
// (from MonoCera: brs2-brs5)
lemma {:rw} {:teq} select_current_trace_reset_add_keep(a0: array<int, int>, j: int, n: int, c: int, P: (int) -> bool, G: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case k == 0 => a[j := c] case 0 < k && P(k) => a[j := a[j] + G(k)] case 0 < k && !P(k) => a))[j]
      == if n <= 0 then a0[j] else c + sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then (if P(k) then G(k) else 0) else 0))

// an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
// of the predecessor, is the initial element plus the sum of G over the positions before
// (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
lemma {:rw} {:teq} select_current_trace_prefix_sums(b0: array<int, int>, n: int, j: int, G: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := G(k) + b[k]]))[j]
    == if 0 <= j <= n then b0[0] + sum(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k))) else b0[j]

// the same with two added terms, since a higher-order summand matches a single summand only (see TODO.md)
// (from nsqm, nsqmf, pcomp, pcompf, sqm; unused on SV-COMP, whose tasks nsqm, pcomp remain open for other reasons)
lemma {:rw} {:teq} select_current_trace_prefix_sums_add(b0: array<int, int>, n: int, j: int, G: (int) -> int,
                                                 H: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := b[k] + G(k) + H(k)]))[j]
    == if 0 <= j <= n then b0[0] + sum(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k) + H(k))) else b0[j]

// a recurrence in an array: the first cell set to c, each further cell i the previous one plus G(i), so the cell j is
// c plus the sum of G over 1, ..., j, e.g. a[i] = a[i - 1] + 2 and b[i] = b[i - 1] + a[i - 1] of ifeqn1 (needs the
// read a[i - 1] matched as a[k + -1], see Rewrite.summands)
// (from ifeqn1, ifeqn2)
lemma {:rw} {:teq} select_current_trace_recurrence(a0: array<int, int>, n: int, c: int, j: int, G: (int) -> int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, i ::
            case i == 0 => a[0 := c] case 0 < i => a[i := a[i - 1] + G(i)]))[j]
    == if 0 <= j && j < n then c + sum(maps(for ⌊counter(1, 1, j)⌋ yield k :: G(k))) else a0[j]
