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
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: if P(a0[k]) then c else G(a0[k])))

// a loop that stores at each position k a constant chosen by cases on k stores these values
// (from MonoCera: brs2-brs5)
lemma {:rw} {:teq} stores_index_cases(a0: array<int, int>, n: int, c: int, d: int, P: (int) -> bool)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case P(k) => a[k := c] case !P(k) => a[k := d])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: if P(k) then c else d))

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

// the same where the other iterations keep the array, e.g. since the simplifier has reduced sum[0] + a[i] to sum[0]
// for a[i] == 0
// (from MonoCera: ms1, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} select_current_trace_reset_keep(a0: array<int, int>, j: int, n: int, c: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case k == 0 => a[j := c] case 0 < k => a))[j]
      == if n <= 0 then a0[j] else c

// a read at a position other than that of an update, also where the simplifier does not decide that they differ, from
// a fact j != i
// (from array_of_struct_single_elem_init, single_elem_safe)
lemma {:rw} {:teq} select_store_other<a, b>(a: array<a, b>, i: a, v: b, j: a)
  requires j != i
  ensures a[i := v][j] == a[j]

// the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
// values; both counters are patterns, since they are different trace variables in programs
// (from conda, condaf, ss1, ss1f; used on SV-COMP by revcpyswp2 only)
lemma {:rw} {:teq} selects_stores_counter(a: array<int, int>, i: int, c: int, n: int, vs: List<int>)
  requires c != 0
  ensures selects(current(stores(a, ⌊counter(i, c, n)⌋, vs)), ⌊counter(i, c, n)⌋) == vs

// stores at the positions of a counter, guarded by C, keep the other positions; a read at j; the case that keeps the
// array is no store, so the fold stores does not apply (ideas/conditional-stores.md)
// (from copysome1-1, copysome1-2; used on SV-COMP by copysome1-1 only)
lemma {:rw} {:teq} select_current_trace_conditional_store(a0: array<int, int>, n: int, j: int, C: (int) -> bool,
                                                   V: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case C(k) => a[k := V(k)] case !C(k) => a))[j]
      == if 0 <= j < n && C(j) then V(j) else a0[j]

// the same, with the guard and the value on the values of three further dependencies at the iteration of j
// (from array_mul_init; used on SV-COMP by array_mul_init, motivex only)
lemma {:rw} {:teq} select_current_trace_conditional_store_deps(a0: array<int, int>, n: int, j: int, hs: List<int>,
                                                        cs: List<int>, vs: List<int>, C: (int, int, int) -> bool,
                                                        V: (int, int, int) -> int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs, cs, vs do a, k, h, c, v ::
                  case C(h, c, v) => a[k := V(h, c, v)] case !C(h, c, v) => a))[j]
    == if 0 <= j < n && C(earlier(j, hs), earlier(j, cs), earlier(j, vs))
       then V(earlier(j, hs), earlier(j, cs), earlier(j, vs))
       else a0[j]

// a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
// iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
// (from condn, condnf; used on SV-COMP by condn only)
lemma {:rw} {:teq} select_current_trace_cap(a0: array<int, int>, n: int, j: int, b: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case a[k] < b => a case b <= a[k] => a[k := b]))[j]
    == if 0 <= j < n && b <= a0[j] then b else a0[j]

// a copy from both ends: iteration k copies the positions m - k - 1 and k from b, so a position covered by either
// range holds b at it, whatever the order of the stores and whether the ranges overlap; the index as the simplifier
// normalizes it, and the source an array or the list of values of an earlier loop, since a higher-order value
// F(m - k - 1) does not match (TODO.md)
// (from array-tiling/tcpy, array-cav19/array_tiling_tcpy)
lemma {:rw} {:teq} select_current_trace_copy_both_ends(a0: array<int, int>, b: array<int, int>, n: int, m: int, j: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[-k + m + -1 := b[-k + m + -1]][k := b[k]]))[j]
    == if 0 <= j < n || m - n <= j < m then b[j] else a0[j]

// (from array-tiling/tcpy)
lemma {:rw} {:teq} select_current_trace_copy_both_ends_list(a0: array<int, int>, xs: List<int>, n: int, m: int,
                                                            j: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  a[-k + m + -1 := earlier(-k + m + -1, xs)][k := earlier(k, xs)]))[j]
    == if 0 <= j < n || m - n <= j < m then earlier(j, xs) else a0[j]

// a store of the old value of a cell after a store at another position changes nothing, e.g. volArray[2 k + 1] =
// volArray[2 k + 1] after volArray[2 k] = c
// (from mbpr2)
lemma {:rw} {:teq} store_select_other(a: array<int, int>, i: int, j: int, v: int)
  requires i != j
  ensures a[i := v][j := a[j]] == a[i := v]
