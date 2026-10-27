// multisets: the folds that do not depend on the order of a list as folds of its multiset (the multisets of the core,
// cvc5's bags), and the permutations of arrays (a swap, a rotation) as lemmas on the multisets of their values, such
// that a fold of a permuted array is the same term as that of the original; an optional module over teq.dfy
// (-include teq:multisets) after teq:aggregation, whose lemmas on lists apply first (ideas/multisets.md); the lemmas
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

// a fold of the values read at keys is the fold of their multiset; only for reads at keys, where the permutations of
// arrays occur, not for all lists: a conversion of every sum or maximum preempts the rules of teq:aggregation on the
// comparisons around them, since rewriting is innermost (cloud, Oct 27: 27 tasks of Loops lost, sqrt1, ps2-ps6)
// (from reducercommutativity: sum, avg, sep)
lemma {:rw} {:teq} sum_selects_elems(a: array<int, int>, keys: List<int>)
  ensures sum(selects(a, keys)) == msum(elems(selects(a, keys)))

lemma {:rw} {:teq} parity_selects_elems(a: array<int, int>, keys: List<int>)
  ensures parity(selects(a, keys)) == mparity(elems(selects(a, keys)))

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
