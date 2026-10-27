// searching: the abstractions of the iteration constraints of linear searches (agreeing prefixes, no occurrence in a
// prefix or among the values read at a counter, values above the iterations) with their facts at the reads, and the
// bisection of an interval with a probe, whose bounds are the cuts of its guards (cut, declared in teq.dfy); an
// optional module over teq.dfy (-include teq:search); the facts at the reads are rules on the comparisons of the
// reads that the goals contain, whose other variables are bound by the facts of the abstractions (side conditions
// looked up among the facts), not forward lemmas, which would fire at every read

// the first n values of xs and ys agree: the iteration constraint that they are equal at the iterations 0, ..., n - 1 is
// the equation of their prefixes
// (from standard_compare_ground)
lemma {:rw} {:teq} invs_agree_prefix(n: int, xs: List<int>, ys: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: earlier(k, xs) == earlier(k, ys)) <==> prefix(n, xs) == prefix(n, ys)

// lists whose prefixes of length n are equal agree at each position below n, a rule on the comparison of the reads
// (from standard_compare_ground)
lemma {:rw} {:teq} earlier_eq_prefix(j: int, n: int, xs: List<int>, ys: List<int>)
  requires prefix(n, xs) == prefix(n, ys) && 0 <= j < n
  ensures (earlier(j, xs) == earlier(j, ys)) <==> true

// a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
// (from standard_find_ground-1)
lemma {:rw} {:teq} not_occurs_prefix(n: int, e: int, xs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: earlier(k, xs) != e) <==> !occurs(e, prefix(n, xs))

// the first n values of ts exceed their positions: folded from the iteration constraint that the values of the
// iterations exceed the iterations
// (from simple_array_index_value_2)
function {:teq} {:fold} above_iterations(n: int, ts: List<int>): bool
{
  invs(for ⌊counter(0, 1, n)⌋, ts check k, t :: k < t)
}

// a value that does not occur in the prefix of length n differs from the reads at the positions in that range
// (from standard_find_ground-1, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} earlier_eq_not_occurs_prefix(j: int, n: int, e: int, xs: List<int>)
  requires !occurs(e, prefix(n, xs)) && 0 <= j < n
  ensures (earlier(j, xs) == e) <==> false

// the reads at the positions in the range exceed the positions
// (from simple_array_index_value_2; unused on SV-COMP)
lemma {:rw} {:teq} earlier_above_iterations(j: int, n: int, ts: List<int>)
  requires above_iterations(n, ts) && 0 <= j < n
  ensures (j < earlier(j, ts)) <==> true

// a sentinel: the reads of an array where x is stored at j differ from x at the positions i, ..., i + n - 1 exactly if
// j is not among them and the reads of the array before differ from x there; a rule on the iteration constraint of
// the search, before not_occurs_selects folds it
// (from standard_sentinel-2, loop-acceleration/array_4)
lemma {:rw} {:teq} invs_select_store_ne(x: int, a: array<int, int>, j: int, i: int, n: int)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: a[j := x][k] != x)
    <==> !(i <= j && j < i + n) && invs(for ⌊counter(i, 1, n)⌋ check k :: a[k] != x)

lemma {:rw} {:teq} not_occurs_selects(a: array<int, int>, x: int, i: int, n: int)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: a[k] != x) <==> !occurs(x, selects(a, ⌊counter(i, 1, n)⌋))

// a value that does not occur among the reads of a counter differs from the reads at the positions in its range
// (used on SV-COMP by n.c40, str_cpy only)
lemma {:rw} {:teq} select_eq_not_occurs_selects(k: int, a: array<int, int>, x: int, i: int, n: int)
  requires !occurs(x, selects(a, ⌊counter(i, 1, n)⌋)) && i <= k < i + n
  ensures (a[k] == x) <==> false

// a bisection of [l0, h0) with a probe M strictly inside the interval: while lo < hi, lo moves above the probe where
// G holds and hi down to it where H holds; named by bisection, which keeps the probe and the guards (folded); the
// second case excludes G, such that the cases are disjoint, and the third keeps the state where lo < hi fails or no
// guard holds, such that they are complete; the traces of the loops have no such case, the fold matches them since
// their guards are disjoint and their iteration constraints exclude the third case in their updates
// (unused on SV-COMP; for the binary search of examples/dafny/algorithms/bsearch.dfy)
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
// (unused on SV-COMP; for the binary search of examples/dafny/algorithms/bsearch.dfy)
lemma {:fw} {:teq} bisection_lo(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall l: int, h: int :: l < h ==> l <= M(l, h) && M(l, h) < h
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && G(q) ==> G(p)
  ensures l0 <= current(bisection(l0, h0, ks, M, G, H)).0 <= cut(G, l0, h0)

// (unused on SV-COMP; for the binary search of examples/dafny/algorithms/bsearch.dfy)
lemma {:fw} {:teq} bisection_hi(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall l: int, h: int :: l < h ==> l <= M(l, h) && M(l, h) < h
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && H(p) ==> H(q)
  ensures cut((j: int) => !H(j), l0, h0) <= current(bisection(l0, h0, ks, M, G, H)).1 <= h0
