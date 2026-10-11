// searching: the abstractions of iteration constraints of searches (agreeing prefixes, no occurrence in a prefix,
// values above the iterations) and their instantiation at a position extracted from teq.dfy on Oct 11, 2026 as one of
// its modules, teq.dfy itself is unchanged; this file assumes the core declarations of teq.dfy (Nat, integer, natural,
// List, length, unspecified, Trace, current, butlast, counter, earlier, prefix, occurs, indexof, distincts, consts),
// counters.dfy, and arrays.dfy (selects); the attributes and the order of the lemmas are those of teq.dfy; the assembly
// of the preludes from the modules is not implemented yet, and the modules are not tested

// the first n values of xs and ys agree
function {:teq} agree_prefix(n: Nat, xs: List<int>, ys: List<int>): bool
{
  match n
  case zero => true
  case succ(m) => agree_prefix(m, xs, ys) && earlier(m, xs) == earlier(m, ys)
}

// the first n values of ts exceed their positions
function {:teq} above_iterations(n: Nat, ts: List<int>): bool
{
  match n
  case zero => true
  case succ(m) => above_iterations(m, ts) && integer(m) < earlier(m, ts)
}

// two sequences that are equal at the iterations 0, ..., n - 1 agree there
// (from standard_compare_ground)
lemma {:rw} {:teq} agree_prefix_def(n: Nat, xs: List<int>, ys: List<int>, hs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(natural(k), xs) == earlier(natural(k), ys))
    <==> agree_prefix(n, xs, ys)

// a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
// (from standard_find_ground-1)
lemma {:rw} {:teq} not_occurs_prefix_def(n: Nat, e: int, xs: List<int>, hs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(natural(k), xs) != e) <==> !occurs(e, prefix(n, xs))

// the same for reads of an array at the positions of a counter: x does not occur among the values read there
// (from lsearch)
lemma {:rw} {:teq} not_occurs_selects_def(a: array<int, int>, x: int, i: int, n: Nat)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: a[k] != x) <==> !occurs(x, selects(a, ⌊counter(i, 1, n)⌋))

// the values of the iterations exceed the iterations
// (from simple_array_index_value_2)
lemma {:rw} {:teq} above_iterations_def(n: Nat, ts: List<int>, hs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, ts check k, h, t :: k < t) <==> above_iterations(n, ts)

// agreeing sequences are equal at each position in the range; the atom is the left-hand side
// (from standard_compare_ground)
lemma {:rw} {:teq} earlier_agree_prefix(n: Nat, j: Nat, xs: List<int>, ys: List<int>)
  requires agree_prefix(n, xs, ys) && integer(j) < integer(n)
  ensures (earlier(j, xs) == earlier(j, ys)) <==> true

// which is instantiated at the positions j in that range
// (from standard_find_ground-1)
lemma {:rw} {:teq} earlier_not_occurs_prefix(n: Nat, j: Nat, e: int, xs: List<int>)
  requires !occurs(e, prefix(n, xs)) && integer(j) < integer(n)
  ensures (earlier(j, xs) == e) <==> false

// the same for reads of an array, at the positions k of the counter
// (from lsearch)
lemma {:rw} {:teq} select_not_occurs_selects(a: array<int, int>, x: int, i: int, n: Nat, k: int)
  requires !occurs(x, selects(a, ⌊counter(i, 1, n)⌋)) && i <= k < i + integer(n)
  ensures (a[k] == x) <==> false

// a sentinel: a position j that holds x, which does not occur among the values read at the positions 0, ..., n - 1,
// is at least n
// (from standard_sentinel-2)
lemma {:rw} {:teq} select_not_occurs_selects_beyond(n: Nat, j: int, x: int, a: array<int, int>)
  requires !occurs(x, selects(a, ⌊counter(0, 1, n)⌋)) && a[j] == x && 0 <= j
  ensures integer(n) <= j

// which is instantiated at the positions j in the range
// (from simple_array_index_value_2)
lemma {:rw} {:teq} earlier_above_iterations(n: Nat, j: Nat, ts: List<int>)
  requires above_iterations(n, ts) && integer(j) < integer(n)
  ensures (integer(j) < earlier(j, ts)) <==> true
