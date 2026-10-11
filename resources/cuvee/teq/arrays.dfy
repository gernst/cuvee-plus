// array acceleration: the traces of stores and shifts, the reads of arrays at the positions of counters (selects), the
// reads of their current and earlier values, conditional stores, caps, and recurrences that fill an array extracted
// from teq.dfy on Oct 11, 2026 as one of the modules that -teq injects in the order of TEQ.modules, teq.dfy itself is
// kept but not injected; this file assumes the core declarations of teq.dfy (Nat, integer, natural, List, length,
// unspecified, Trace, current, butlast, counter, earlier, prefix, occurs, indexof, distincts, consts), counters.dfy,
// and aggregation.dfy (sum); the attributes and the order of the lemmas are those of teq.dfy

// the trace of the successive stores of the values at the keys into a
function {:teq} {:fold} stores<a, b>(a: array<a, b>, keys: List<a>, values: List<b>): Trace<array<a, b>>
{
  trace(a, for keys, values do b, k, v :: b[k := v])
}

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

// the trace of the successive copies a[k] := a[k + d] for the keys, which is modeled for increasing keys and
// nonnegative offsets only, where the entries read are not yet modified
function {:teq} {:fold} shifts(a: array<int, int>, keys: List<int>, d: int): Trace<array<int, int>>
{
  trace(a, for keys do b, k :: b[k := b[k + d]])
}

// stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
// array
// (from standard_palindrome_ground)
lemma {:rw} {:teq} stores_def_read_unmodified(a0: array<int, int>, n: Nat, hs: List<int>, F: (int, int) -> int)
  requires invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: integer(n) <= F(k, h))
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := a[F(k, h)]])
    == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a0[F(k, h)]))

// the same for a sum kept in the cell j of an array, e.g. sum[0] of a one-element array in C: only the cell j is
// written, hence it is read from the final array
// (from MonoCera: brs1-brs5, ms2-ms5)
lemma {:rw} {:teq} select_current_trace_reset_add(a0: array<int, int>, j: int, n: Nat, c: int, G: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case k == 0 => a[j := c] case 0 < k => a[j := a[j] + G(k)]))[j]
      == if n == zero then a0[j] else c + sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then G(k) else 0))

// the same where the other iterations keep the array, e.g. since the simplifier has reduced sum[0] + a[i] to sum[0]
// for a[i] == 0
// (from MonoCera: ms1)
lemma {:rw} {:teq} select_current_trace_reset_keep(a0: array<int, int>, j: int, n: Nat, c: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case k == 0 => a[j := c] case 0 < k => a))[j]
      == if n == zero then a0[j] else c

lemma {:rw} {:teq} earlier_selects<a, b>(j: Nat, a: array<a, b>, keys: List<a>)
  ensures earlier(j, selects(a, keys))
    == a[earlier(j, keys)]

// a read at a position other than that of an update, also where the simplifier does not decide that they differ, from
// a fact j != i
// (from array_of_struct_single_elem_init, single_elem_safe)
lemma {:rw} {:teq} select_store_other<a, b>(a: array<a, b>, i: a, v: b, j: a)
  requires j != i
  ensures a[i := v][j] == a[j]

lemma {:rw} {:teq} prefix_selects<a, b>(k: Nat, a: array<a, b>, keys: List<a>)
  ensures prefix(k, selects(a, keys))
    == selects(a, prefix(k, keys))

lemma {:rw} {:teq} prefix_stores<a, b>(k: Nat, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures prefix(k, ⌊stores(a, keys, values)⌋)
    == ⌊stores(a, prefix(k, keys), prefix(k, values))⌋

// a value read at one of the keys occurs among the values read at them
lemma {:rw} {:teq} occurs_selects<a, b>(k: a, a: array<a, b>, keys: List<a>)
  requires occurs(k, keys)
  ensures occurs(a[k], selects(a, keys))

lemma {:rw} {:teq} selects_stores<a, b>(a: array<a, b>, keys: List<a>, values: List<b>)
  requires distincts(keys)
  ensures selects(current(stores(a, keys, values)), keys)
    == values

lemma {:rw} {:teq} selects_shifts(a: array<int, int>, n: Nat, i: int, d: int)
  requires 0 <= d
  ensures selects(current(shifts(a, ⌊counter(i, 1, n)⌋, d)), ⌊counter(i, 1, n)⌋)
    == selects(a, ⌊counter(i + d, 1, n)⌋)

// the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
// values; both counters are patterns, since they are different trace variables in programs
// (from conda, condaf, ss1, ss1f)
lemma {:rw} {:teq} selects_stores_counter(a: array<int, int>, i: int, c: int, n: Nat, vs: List<int>)
  requires c != 0
  ensures selects(current(stores(a, ⌊counter(i, c, n)⌋, vs)), ⌊counter(i, c, n)⌋) == vs

lemma {:rw} {:teq} current_stores<a, b>(k: a, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures current(stores(a, keys, values))[k]
    == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]

// an earlier state reads the value stored last at k among the keys stored so far, the initial value otherwise
// (indexof is the *last* occurrence, hence indexof(k, prefix(j, keys)) <= indexof(k, keys) but not equal)
lemma {:rw} {:teq} earlier_stores<a, b>(k: a, j: Nat, a: array<a, b>, keys: List<a>, values: List<b>)
  ensures earlier(j, ⌊stores(a, keys, values)⌋)[k]
    == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]

lemma {:rw} {:teq} current_shifts(a: array<int, int>, n: Nat, i: int, d: int, k: int)
  requires 0 <= d
  ensures current(shifts(a, ⌊counter(i, 1, n)⌋, d))[k]
    == if i <= k < i + integer(n) then a[k + d] else a[k]

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

// the same, at distinct positions ps, which are kept as matched, read by occurs and indexof
// (from array_monotonic)
lemma {:rw} {:teq} current_trace_conditional_store_distinct(a0: array<int, int>, n: Nat, j: int, ps: List<int>,
                                                            cs: List<int>, C: (int, int) -> bool, V: (int, int) -> int)
  requires distincts(ps)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, ps, cs do a, k, p, c ::
                          case C(p, c) => a[p := V(p, c)] case !C(p, c) => a))[j]
    == if occurs(j, ps) && C(j, earlier(indexof(j, ps), cs))
       then V(j, earlier(indexof(j, ps), cs))
       else a0[j]

// a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
// iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
// (from condn, condnf)
lemma {:rw} {:teq} current_trace_cap(a0: array<int, int>, n: Nat, j: int, b: int, hs: List<int>)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case a[k] < b => a case b <= a[k] => a[k := b]))[j]
    == if 0 <= j < integer(n) && b <= a0[j] then b else a0[j]

// an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
// of the predecessor, is the initial element plus the sum of G over the positions before
// (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
lemma {:rw} {:teq} current_trace_prefix_sums(b0: array<int, int>, n: Nat, j: int, G: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := G(k) + b[k]]))[j]
    == if 0 <= j <= integer(n) then b0[0] + sum(maps(for ⌊counter(0, 1, natural(j))⌋ yield k :: G(k))) else b0[j]

// the same with two added terms, since a higher-order summand matches a single summand only (see TODO.md)
// (from nsqm, nsqmf, pcomp, pcompf, sqm)
lemma {:rw} {:teq} current_trace_prefix_sums_add(b0: array<int, int>, n: Nat, j: int, G: (int) -> int,
                                                 H: (int) -> int)
  ensures current(trace(b0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do b, k, i :: b[i := b[k] + G(k) + H(k)]))[j]
    == if 0 <= j <= integer(n) then b0[0] + sum(maps(for ⌊counter(0, 1, natural(j))⌋ yield k :: G(k) + H(k))) else b0[j]

// the special case of a constant added term
// (from standard_seq_init_ground)
lemma {:rw} {:teq} current_trace_prefix_const(a0: array<int, int>, n: Nat, c: int, j: int)
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do a, k, i :: a[i := a[k] + c]))[j]
    == if 1 <= j <= integer(n) then a0[0] + j * c else a0[j]
