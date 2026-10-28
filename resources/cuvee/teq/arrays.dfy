// arrays: stores at the positions of a counter and of distinct keys, conditional stores and resets, the reads of an
// array updated along a trace, the rows of two-dimensional arrays, copies from both ends; an optional module over
// teq.dfy (-include teq:arrays); the folds stores and selects and their reads are in teq.dfy, the recurrences with sums
// in aggregation

// each key is visited once only if they are distinct, hence b[k] is still the initial value a[k],
// in any context f of the read, which may depend on the other dependencies, but not on the accumulator otherwise
lemma {:rw} {:teq} trace_read_initial<a, b>(a: array<a, b>, keys: List<a>, fs: List<b -> b>)
  requires distincts(keys)
  ensures trace(a, for keys, fs do b, k, f :: b[k := f(b[k])])
    == trace(a, for keys, fs do b, k, f :: b[k := f(a[k])])

// an inner loop that updates the row r of a two-dimensional array only, cell by cell, is an update of that row by a
// trace over the row, whose stores fold as those of a one-dimensional array; the outer loop over the rows then
// updates each row once, which trace_read_initial reads from the initial array
// (from array-multidimensional: init-2-n-u, init-non-constant-2-n-u, copy-2-u, copy-partial-2-n-u, rev-2-n-u)
lemma {:rw} {:teq} current_trace_row(A0: array<int, array<int, int>>, r: int, n: int, V: (int) -> int)
  ensures current(trace(A0, for ⌊counter(0, 1, n)⌋ do A, j :: A[r := A[r][j := V(j)]]))
    == A0[r := current(trace(A0[r], for ⌊counter(0, 1, n)⌋ do b, j :: b[j := V(j)]))]

// a loop that updates each position once, by cases on its old value, stores the values computed from the initial
// array, since a[k] is not modified before iteration k; the first case stores a constant, since a higher-order
// instance must contain the term it abstracts, a[k] (see Rewrite.abstraction); a workaround for two gaps of the
// engine, like the conditional stores below (ideas/conditional-stores.md)
// (from MonoCera: conda, s1lif-s5lif)
lemma {:rw} {:teq} stores_cases(a0: array<int, int>, n: int, c: int, P: (int) -> bool, G: (int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case P(a[k]) => a[k := c] case !P(a[k]) => a[k := G(a[k])])
      == stores(a0, ⌊counter(0, 1, n)⌋,
                maps(for ⌊counter(0, 1, n)⌋ yield k :: case P(a0[k]) => c case !P(a0[k]) => G(a0[k])))

// a loop whose iteration k stores F(k) at k by two cases split at a position c, where the simplifier has substituted
// c for k in the second case, so that the cases are not merged (TODO.md, ideas/dnf-guards.md)
// (from copysome2-1, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} stores_cases_point(a0: array<int, int>, n: int, c: int, F: (int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case k != c => a[k := F(k)] case k == c => a[c := F(c)])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: F(k)))

// stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
// array
// (from standard_palindrome_ground, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} stores_read_unmodified(a0: array<int, int>, n: int, hs: List<int>, F: (int, int) -> int)
  requires invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: n <= F(k, h))
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := a[F(k, h)]])
    == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a0[F(k, h)]))

// a loop that moves each element of i + 1, ..., i + n one position down reads the next element of the initial array at
// the positions it writes, i, ..., i + n - 1, which it has not written yet, and the initial array elsewhere
// (from reducercommutativity, array-crafted bAnd, bor, xor: the rotation)
lemma {:rw} {:teq} select_current_shifts(a: array<int, int>, i: int, n: int, j: int)
  requires 0 <= n
  ensures current(shifts(a, ⌊counter(i, 1, n)⌋))[j]
    == if {
      case i <= j < i + n => a[j + 1]
      case !(i <= j < i + n) => a[j]
    }

// the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
// values; both counters are patterns, since they are different trace variables in programs
// (from conda, condaf, ss1, ss1f; used on SV-COMP by revcpyswp2 only)
lemma {:rw} {:teq} selects_stores_counter(a: array<int, int>, i: int, c: int, n: int, vs: List<int>)
  requires c != 0
  ensures selects(current(stores(a, ⌊counter(i, c, n)⌋, vs)), ⌊counter(i, c, n)⌋) == vs

// stores at the keys where a guard holds, the other positions kept: the case that keeps the array is no store, so the
// fold stores does not apply; the guards and the values are lists, which the matcher synthesizes over the dependencies
// they read, e.g. the index, choices, or other arrays (ideas/conditional-stores.md)
function {:teq} {:fold} stores_where(a: array<int, int>, keys: List<int>, guards: List<bool>, values: List<int>):
    Trace<array<int, int>>
{
  trace(a, for keys, guards, values do b, k, g, v :: case g => b[k := v] case !g => b)
}

lemma {:rw} {:teq} length_stores_where(a: array<int, int>, keys: List<int>, guards: List<bool>, values: List<int>)
  ensures length(⌊stores_where(a, keys, guards, values)⌋) == length(keys)

lemma {:rw} {:teq} earlier_stores_where(j: int, a: array<int, int>, keys: List<int>, guards: List<bool>,
    values: List<int>)
  ensures earlier(j, ⌊stores_where(a, keys, guards, values)⌋)
    == current(stores_where(a, prefix(j, keys), prefix(j, guards), prefix(j, values)))

lemma {:rw} {:teq} prefix_stores_where(k: int, a: array<int, int>, keys: List<int>, guards: List<bool>,
    values: List<int>)
  ensures prefix(k, ⌊stores_where(a, keys, guards, values)⌋)
    == ⌊stores_where(a, prefix(k, keys), prefix(k, guards), prefix(k, values))⌋

// a read at distinct keys: the value of the iteration of j if its guard holds, otherwise the initial value
// (from copysome1-1, copysome1-2, copysome2-1, array_mul_init, motivex)
lemma {:rw} {:teq} select_current_stores_where(a0: array<int, int>, keys: List<int>, guards: List<bool>,
    values: List<int>, j: int)
  requires distincts(keys)
  ensures current(stores_where(a0, keys, guards, values))[j]
    == if {
      case occurs(j, keys) && earlier(indexof(j, keys), guards) => earlier(indexof(j, keys), values)
      case !(occurs(j, keys) && earlier(indexof(j, keys), guards)) => a0[j]
    }

// stores at one key j, guarded to the first iteration only: a reset of a cell where the other iterations keep the
// array, e.g. since the simplifier has reduced sum[0] + a[i] to sum[0] for a[i] == 0; the keys are not distinct
// (from MonoCera: ms1, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} select_current_stores_where_first(a0: array<int, int>, n: int, j: int, values: List<int>)
  ensures current(stores_where(a0, ⌊consts(n, j)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: k == 0), values))[j]
    == if {
      case n <= 0 => a0[j]
      case 0 < n => earlier(0, values)
    }

// a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
// iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
// (from condn, condnf; used on SV-COMP by condn only)
lemma {:rw} {:teq} select_current_trace_cap(a0: array<int, int>, n: int, j: int, b: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case a[k] < b => a case b <= a[k] => a[k := b]))[j]
    == if {
      case 0 <= j < n && b <= a0[j] => b
      case !(0 <= j < n && b <= a0[j]) => a0[j]
    }

// copies of the values of a source S at the keys of two lists per iteration, e.g. a copy from both ends, positions
// m - k - 1 and k: each position takes the value of the source at itself, so the order of the stores does not matter,
// nor whether the keys overlap; S is the source read at its position, an array b[p] or the list of values of an
// earlier loop earlier(p, xs)
function {:teq} {:fold} copies(a: array<int, int>, ks: List<int>, ls: List<int>, S: (int) -> int):
    Trace<array<int, int>>
{
  trace(a, for ks, ls do b, p, q :: b[p := S(p)][q := S(q)])
}

lemma {:rw} {:teq} length_copies(a: array<int, int>, ks: List<int>, ls: List<int>, S: (int) -> int)
  ensures length(⌊copies(a, ks, ls, S)⌋) == length(ks)

lemma {:rw} {:teq} earlier_copies(j: int, a: array<int, int>, ks: List<int>, ls: List<int>, S: (int) -> int)
  ensures earlier(j, ⌊copies(a, ks, ls, S)⌋)
    == current(copies(a, prefix(j, ks), prefix(j, ls), S))

lemma {:rw} {:teq} prefix_copies(k: int, a: array<int, int>, ks: List<int>, ls: List<int>, S: (int) -> int)
  ensures prefix(k, ⌊copies(a, ks, ls, S)⌋)
    == ⌊copies(a, prefix(k, ks), prefix(k, ls), S)⌋

// a position among the keys holds the source at it, the others the initial value
// (from array-tiling/tcpy, array-cav19/array_tiling_tcpy)
lemma {:rw} {:teq} select_current_copies(a0: array<int, int>, ks: List<int>, ls: List<int>, S: (int) -> int, j: int)
  ensures current(copies(a0, ks, ls, S))[j]
    == if {
      case occurs(j, ks) || occurs(j, ls) => S(j)
      case !(occurs(j, ks) || occurs(j, ls)) => a0[j]
    }

// a store of the old value of a cell after a store at another position changes nothing, e.g. volArray[2 k + 1] =
// volArray[2 k + 1] after volArray[2 k] = c
// (from mbpr2)
lemma {:rw} {:teq} store_select_other(a: array<int, int>, i: int, j: int, v: int)
  requires i != j
  ensures a[i := v][j := a[j]] == a[i := v]
