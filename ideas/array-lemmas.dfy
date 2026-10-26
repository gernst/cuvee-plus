// lemmas for open tasks of SV-COMP ReachSafety-Arrays that stay out of the lemma database (ideas/array-lemmas.md):
// workarounds for gaps of the engine, each with the fix it waits for, and a lemma that only one task needs; injected by
// -include, e.g.
//   ./Cuvee.sh -svcomp -rules -include ideas/array-lemmas.dfy sv-benchmarks/c/array-examples/standard_partial_init_ground.i
// the file is parsed on its own, hence it repeats the declarations of teq.dfy and aggregation.dfy that it needs,
// exactly as there; not proved in Lean

// declarations of teq.dfy

datatype {:teq} {:lean} List<a₀> = nil | cons(head: a₀, tail: List<a₀>)

const {:teq} unspecified<a₀>: a₀

datatype {:teq} Trace<a₀> = stop(last: a₀) | step(first: a₀, rest: Trace<a₀>)

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

// declarations of aggregation.dfy

function {:teq} {:fold} maxs(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case m < v => v case v <= m => m)
}

function {:teq} {:fold} mins(x: int, values: List<int>): Trace<int>
{
  trace(x, for values do m, v :: case v < m => v case m <= v => m)
}

function {:rw} {:teq} count<a>(e: a, vs: List<a>): int
{
  match vs
  case nil => 0
  case cons(v, ws) => (if v == e then 1 else 0) + count(e, ws)
}

function {:teq} {:fold} counts<a>(x: int, e: a, vs: List<a>): Trace<int>
{
  trace(x, for vs do y, v :: case v == e => y + 1 case v != e => y)
}

// declaration of teq.dfy

function {:teq} {:fold} stores<a, b>(a: array<a, b>, keys: List<a>, values: List<b>): Trace<array<a, b>>
{
  trace(a, for keys, values do b, k, v :: b[k := v])
}

// compactions and filters: a store at a position counted by the iterations where a guard holds, C[j++] = i or
// bb[b++] = aa[a]; the folds keep the keys as a list ⌊K⌋ and the counts are variables of the conditions, matched against
// the facts, since the arithmetic compares terms with binders literally, not modulo the names of the bound variables,
// and ⌊K⌋ is not identified with ⌊counter(0, 1, n)⌋ below a binder (engine: comparison modulo bound names, congruence
// through binders)

// a compaction: the iterations k where P(k) holds are stored at the positions 0, 1, ... in the order of the loop, the
// position j counting them; the fold keeps the keys as they are, a list ⌊K⌋, such that the count in the conditions of
// the lemmas is that of the program, not one over ⌊counter(0, 1, n)⌋, which the arithmetic does not identify with it
// (from standard_partial_init_ground)
function {:teq} {:fold} compact(c0: array<int, int>, ks: List<int>, P: (int) -> bool): Trace<array<int, int>>
{
  trace(c0, for ks, ⌊counts(0, true, maps(for ks yield k :: P(k)))⌋ do c, k, j :: case P(k) => c[j := k] case !P(k) => c)
}

// the x-th of them is at least x, and at most x plus the iterations without P after it; the count m is a variable of
// the conditions, matched against the facts, since the arithmetic compares terms with binders literally, not modulo
// the names of the bound variables
lemma {:rw} compact_lower(c0: array<int, int>, K: Trace<int>, n: int, m: int, x: int, P: (int) -> bool)
  requires K == counter(0, 1, n)
  requires m == count(true, maps(for ⌊K⌋ yield k :: P(k)))
  requires 0 <= x < m
  ensures x <= current(compact(c0, ⌊K⌋, P))[x]

lemma {:rw} compact_upper(c0: array<int, int>, K: Trace<int>, n: int, m: int, x: int, P: (int) -> bool)
  requires K == counter(0, 1, n)
  requires m == count(true, maps(for ⌊K⌋ yield k :: P(k)))
  requires 0 <= x < m
  ensures current(compact(c0, ⌊K⌋, P))[x] + m <= x + n

// a filter: the values F(k) of the iterations k where b <= F(k) holds are stored at the positions 0, 1, ..., the
// position j counting them, hence the first m positions, for the count m, hold values not below b
// (from standard_partition_ground-2, standard_partition_original_ground)
function {:teq} {:fold} filter_above(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int): Trace<array<int, int>>
{
  trace(c0, for ks, ⌊counts(0, true, maps(for ks yield k :: b <= F(k)))⌋ do c, k, j ::
        case b <= F(k) => c[j := F(k)] case F(k) < b => c)
}

lemma {:rw} filter_above_select(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int, m: int, x: int)
  requires m == count(true, maps(for ks yield k :: b <= F(k)))
  requires 0 <= x < m
  ensures b <= current(filter_above(c0, ks, b, F))[x]

// the same for the values below b, e.g. in the else branch, whose count is the iterations minus the count of the
// others, as counts_false states it
function {:teq} {:fold} filter_below(c0: array<int, int>, ks: List<int>, b: int, F: (int) -> int): Trace<array<int, int>>
{
  trace(c0, for ks, ⌊counts(0, false, maps(for ks yield k :: b <= F(k)))⌋ do c, k, j ::
        case b <= F(k) => c case F(k) < b => c[j := F(k)])
}

lemma {:rw} filter_below_select(c0: array<int, int>, K: Trace<int>, n: int, b: int, F: (int) -> int, m: int, x: int)
  requires K == counter(0, 1, n)
  requires count(true, maps(for ⌊K⌋ yield k :: b <= F(k))) + m == n
  requires 0 <= x < m
  ensures current(filter_below(c0, ⌊K⌋, b, F))[x] < b

// a maximum seeded with the element before the loop, the only task that needs it

// the maximum seeded with the read at h and continued with the reads at i, ..., i + n - 1, for h = i - 1, bounds the
// reads at h, ..., i + n - 1, e.g. largest = a[0] before a loop from 1
// (from sanfoundry_27_ground)
lemma {:rw} earlier_le_current_maxs_seeded(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures earlier(j, xs) <= current(maxs(earlier(h, xs), maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs))))

lemma {:rw} current_mins_seeded_le_earlier(j: int, h: int, i: int, n: int, xs: List<int>)
  requires h == i - 1 && h <= j < i + n
  ensures current(mins(earlier(h, xs), maps(for ⌊counter(i, 1, n)⌋ yield v :: earlier(v, xs)))) <= earlier(j, xs)

// copies from both ends; the index is written as the simplifier normalizes it (engine: normalize the arithmetic of
// rule patterns as that of goals), and the source is an array or a list, since a higher-order value F(m - k - 1) does
// not match (engine: higher-order variables applied to terms other than bound variables, once bound by another case)

lemma {:rw} select_current_trace_copy_both_ends(a0: array<int, int>, b: array<int, int>, n: int, m: int, j: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[-k + m + -1 := b[-k + m + -1]][k := b[k]]))[j]
    == if 0 <= j < n || m - n <= j < m then b[j] else a0[j]

lemma {:rw} select_current_trace_copy_both_ends_list(a0: array<int, int>, xs: List<int>, n: int, m: int, j: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[-k + m + -1 := earlier(-k + m + -1, xs)][k := earlier(k, xs)]))[j]
    == if 0 <= j < n || m - n <= j < m then earlier(j, xs) else a0[j]

// two cases split at a position, where the simplifier has substituted c for k in the second case (engine: merge cases
// whose results are equal after substituting the equation of the guard, ideas/dnf-guards.md)

// a loop whose iteration k stores F(k) at k, by two cases split at a position c, where the simplifier has
// substituted c for k in the second case, so that the cases are not merged
// (from copysome2-1)
lemma {:rw} stores_cases_point(a0: array<int, int>, n: int, c: int, F: (int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case k != c => a[k := F(k)] case k == c => a[c := F(c)])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: F(k)))

// integer facts that the arithmetic lacks, as forward lemmas at every division and every remainder of a successor
// (engine: division with remainder and parity in the arithmetic of -prove)

// division with remainder, which the arithmetic does not know, e.g. SIZE == 2 * (SIZE / 2) for SIZE % 2 == 0; a fact at
// the divisions
// (from array-tiling/tcpy)
lemma {:fw} div_mod(x: int, c: int)
  requires 0 < c
  ensures x == c * (x / c) + x % c

// consecutive integers have different parities, which the arithmetic does not know; a fact at the remainders of
// successors
// (from array-tiling/mbpr2)
lemma {:fw} mod2_succ(x: int)
  ensures (x + 1) % 2 == 1 - x % 2
