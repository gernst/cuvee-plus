// searching: the abstractions of the iteration constraints of linear searches (agreeing prefixes, no occurrence in a
// prefix or among the values read at a counter, values above the iterations) with their facts at the reads, and the
// bisection of an interval with a probe, whose bounds are the cuts of its guards (cut, declared in teq.dfy); an
// optional module over teq.dfy
// alone (-include teq:search), migrated on Oct 13, 2026 from the module of the per-variable form (in legacy/teq.dfy),
// with the search lemmas of teq.dfy and the bisection of examples/dafny/state/bsearch_bisect.dfy; the facts at the
// reads are forward lemmas, triggered by the read, earlier(j, xs) or a[k], whose other variables are matched against
// the facts of the abstractions

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

// the values of the iterations exceed the iterations
// (from simple_array_index_value_2)
lemma {:rw} {:teq} above_iterations_def(n: Nat, ts: List<int>, hs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, ts check k, h, t :: k < t) <==> above_iterations(n, ts)

// agreeing sequences are equal at each position in the range, a fact at the reads
// (from standard_compare_ground)
lemma {:fw} {:teq} earlier_agree_prefix(n: Nat, j: Nat, xs: List<int>, ys: List<int>)
  requires agree_prefix(n, xs, ys) && integer(j) < integer(n)
  ensures earlier(j, xs) == earlier(j, ys)

// which is instantiated at the positions j in that range
// (from standard_find_ground-1)
lemma {:fw} {:teq} earlier_not_occurs_prefix(n: Nat, j: Nat, e: int, xs: List<int>)
  requires !occurs(e, prefix(n, xs)) && integer(j) < integer(n)
  ensures earlier(j, xs) != e

// a sentinel: a value x stored at a position j occurs among the values read at the positions 0, ..., n - 1, unless j
// is beyond them; a forward fact at the reads, which are the trigger, since the bound integer(n) <= j occurs in the
// goal only as a comparison of the loop variable
// (from standard_sentinel-2)
lemma {:fw} {:teq} store_occurs_selects(n: Nat, j: int, x: int, a: array<int, int>)
  requires 0 <= j
  ensures occurs(x, selects(a[j := x], ⌊counter(0, 1, n)⌋)) || integer(n) <= j

// which is instantiated at the positions j in the range
// (from simple_array_index_value_2)
lemma {:fw} {:teq} earlier_above_iterations(n: Nat, j: Nat, ts: List<int>)
  requires above_iterations(n, ts) && integer(j) < integer(n)
  ensures integer(j) < earlier(j, ts)

lemma {:rw} {:teq} not_occurs_selects_def(a: array<int, int>, x: int, i: int, n: Nat)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: a[k] != x) <==> !occurs(x, selects(a, ⌊counter(i, 1, n)⌋))

lemma {:fw} {:teq} select_not_occurs_selects(a: array<int, int>, x: int, i: int, n: Nat, k: int)
  requires !occurs(x, selects(a, ⌊counter(i, 1, n)⌋)) && i <= k < i + integer(n)
  ensures a[k] != x

// a bisection of [l0, h0) with a probe M strictly inside the interval: while lo < hi, lo moves above the probe where
// G holds and hi down to it where H holds; named by bisection, which keeps the probe and the guards (folded); the
// second case excludes G, such that the cases are disjoint, and the third keeps the state where lo < hi fails or no
// guard holds, such that they are complete; the traces of the loops have no such case, the fold matches them since
// their guards are disjoint and their iteration constraints exclude the third case in their updates
function {:teq} {:fold} bisection(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool,
                          H: int -> bool): Trace<(int, int)>
{
  trace(l0, h0, for ks do lo, hi, k ::
        case G(M(lo, hi)) && lo < hi => M(lo, hi) + 1
        case H(M(lo, hi)) && !G(M(lo, hi)) && lo < hi => lo
        case !(lo < hi) || !(G(M(lo, hi)) || H(M(lo, hi))) => lo,
        case G(M(lo, hi)) && lo < hi => hi
        case H(M(lo, hi)) && !G(M(lo, hi)) && lo < hi => M(lo, hi)
        case !(lo < hi) || !(G(M(lo, hi)) || H(M(lo, hi))) => hi)
}

// if G holds on a prefix of [l0, h0), lo stays within l0 and the cut of G, and if H holds on a suffix, hi stays within
// the cut of its negation and h0
lemma {:fw} {:teq} bisection_lo(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall l: int, h: int :: l < h ==> l <= M(l, h) && M(l, h) < h
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && G(q) ==> G(p)
  ensures l0 <= current(bisection(l0, h0, ks, M, G, H)).0 <= cut(G, l0, h0)

lemma {:fw} {:teq} bisection_hi(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall l: int, h: int :: l < h ==> l <= M(l, h) && M(l, h) < h
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && H(p) ==> H(q)
  ensures cut((j: int) => !H(j), l0, h0) <= current(bisection(l0, h0, ks, M, G, H)).1 <= h0
