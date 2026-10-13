// arrays: stores at the positions of a counter and of distinct keys, conditional stores and resets, the reads of an
// array updated along a trace; an optional module over teq.dfy alone (-include teq:arrays), migrated on Oct 13, 2026
// from the module of the per-variable form (in legacy/teq.dfy): the folds stores and selects and their reads are in
// teq.dfy, the recurrences with sums in aggregation, the rules never applied on SV-COMP (shifts, the prefixes of
// selects and stores, occurs_selects, selects_stores, conditional stores at distinct positions, the constant
// recurrence) are left in the legacy file

// each key is visited once only if they are distinct, hence b[k] is still the initial value a[k],
// in any context f of the read, which may depend on the other dependencies, but not on the accumulator otherwise
lemma {:rw} {:teq} trace_read_initial<a, b>(a: array<a, b>, keys: List<a>, fs: List<b -> b>)
  requires distincts(keys)
  ensures trace(a, for keys, fs do b, k, f :: b[k := f(b[k])])
    == trace(a, for keys, fs do b, k, f :: b[k := f(a[k])])

// a loop that updates each position once, by cases on its old value, stores the values computed from the initial
// array, since a[k] is not modified before iteration k; the first case stores a constant, since a higher-order
// instance must contain the term it abstracts, a[k] (see Rewrite.abstraction)
// (from MonoCera: conda, s1lif-s5lif)
lemma {:rw} {:teq} stores_cases_def(a0: array<int, int>, n: Nat, c: int, P: (int) -> bool, G: (int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case P(a[k]) => a[k := c] case !P(a[k]) => a[k := G(a[k])])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: if P(a0[k]) then c else G(a0[k])))

// a loop that stores at each position k a constant chosen by cases on k stores these values
// (from MonoCera: brs2-brs5)
lemma {:rw} {:teq} stores_index_cases_def(a0: array<int, int>, n: Nat, c: int, d: int, P: (int) -> bool)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case P(k) => a[k := c] case !P(k) => a[k := d])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: if P(k) then c else d))

// stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
// array
// (from standard_palindrome_ground)
lemma {:rw} {:teq} stores_def_read_unmodified(a0: array<int, int>, n: Nat, hs: List<int>, F: (int, int) -> int)
  requires invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: integer(n) <= F(k, h))
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := a[F(k, h)]])
    == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a0[F(k, h)]))

// the same where the other iterations keep the array, e.g. since the simplifier has reduced sum[0] + a[i] to sum[0]
// for a[i] == 0
// (from MonoCera: ms1)
lemma {:rw} {:teq} select_current_trace_reset_keep(a0: array<int, int>, j: int, n: Nat, c: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case k == 0 => a[j := c] case 0 < k => a))[j]
      == if n == zero then a0[j] else c

// a read at a position other than that of an update, also where the simplifier does not decide that they differ, from
// a fact j != i
// (from array_of_struct_single_elem_init, single_elem_safe)
lemma {:rw} {:teq} select_store_other<a, b>(a: array<a, b>, i: a, v: b, j: a)
  requires j != i
  ensures a[i := v][j] == a[j]

// the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
// values; both counters are patterns, since they are different trace variables in programs
// (from conda, condaf, ss1, ss1f)
lemma {:rw} {:teq} selects_stores_counter(a: array<int, int>, i: int, c: int, n: Nat, vs: List<int>)
  requires c != 0
  ensures selects(current(stores(a, ⌊counter(i, c, n)⌋, vs)), ⌊counter(i, c, n)⌋) == vs

// stores at the positions of a counter, guarded by C, keep the other positions; a read at j
// (from copysome1-1, copysome1-2)
lemma {:rw} {:teq} current_trace_conditional_store(a0: array<int, int>, n: Nat, j: int, C: (int) -> bool,
                                                   V: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case C(i) => a[i := V(i)] case !C(i) => a))[j]
      == if 0 <= j < integer(n) && C(j) then V(j) else a0[j]

// the same, with the guard and the value on the values of three further dependencies at the iteration of j
// (from array_mul_init)
lemma {:rw} {:teq} current_trace_conditional_store_deps(a0: array<int, int>, n: Nat, j: int, hs: List<int>,
                                                        cs: List<int>, vs: List<int>, C: (int, int, int) -> bool,
                                                        V: (int, int, int) -> int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs, cs, vs do a, k, h, c, v ::
                  case C(h, c, v) => a[k := V(h, c, v)] case !C(h, c, v) => a))[j]
    == if 0 <= j < integer(n) && C(earlier(natural(j), hs), earlier(natural(j), cs), earlier(natural(j), vs))
       then V(earlier(natural(j), hs), earlier(natural(j), cs), earlier(natural(j), vs))
       else a0[j]

// a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
// iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
// (from condn, condnf)
lemma {:rw} {:teq} current_trace_cap(a0: array<int, int>, n: Nat, j: int, b: int, hs: List<int>)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case a[k] < b => a case b <= a[k] => a[k := b]))[j]
    == if 0 <= j < integer(n) && b <= a0[j] then b else a0[j]
