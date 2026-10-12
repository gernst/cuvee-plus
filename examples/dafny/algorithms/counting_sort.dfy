// ./Cuvee.sh -teq -entry main -simplify examples/dafny/algorithms/counting_sort.dfy
// counting sort of a[0..n) with keys in [0, k): a histogram, its prefix sums as the starting positions, and the
// scatter of the elements; three loops in sequence, whose summaries feed each other
//
// status: verified with -teq -simplify; the precondition on the keys is the atom keys_below(a, n, k) instead of
// forall i :: 0 <= i < n ==> 0 <= a[i] < k, since a quantified side condition is not matched against a quantified
// hypothesis (the vocabulary approach of count_occurrences.dfy); the four loops summarize in sequence: the zeroing is
// stores of consts (teq.dfy), the histogram by current_trace_histogram (the increments at the keys a[k] add the
// counts of the values), the prefix sums of the counts fold into sums over the counts (teq.dfy), and their stores at
// the values are the abstract rank_table(c, a, n, kk) by rank_table_def, which binds kk in the pattern of the
// scatter; the scatter stores a[k] at the position read from the table, which is then incremented, i.e. at its rank
// plus the number of equal elements before it: sorted_scatter and count_scatter state the result on the whole
// stores; the counter of the values' selects is tied by an open trace variable Iv matched against the hypothesis
// I == counter(0, 1, n) (a closed equation ⌊I⌋ == ⌊counter(0, 1, n)⌋ is not decided), the key range by the atom with an
// open bound kb matched against the precondition

function sorted(a: array<int, int>, lo: int, hi: int): bool

// the keys of a[0..n) are in [0, k): the precondition as an atom, since a quantified side condition is not matched
// against a quantified hypothesis
function keys_below(a: array<int, int>, n: int, k: int): bool

// a histogram: the increments at the keys a[k] add the number of occurrences of each value
lemma {:rw} current_trace_histogram(c0: array<int, int>, a: array<int, int>, n: Nat, hs: List<int>, v: int)
  ensures current(trace(c0, for ⌊counter(0, 1, n)⌋, hs do c, k, h :: c[a[k] := c[a[k]] + 1]))[v]
    == c0[v] + count(v, selects(a, ⌊counter(0, 1, n)⌋))

// the table of start positions: for the values v below kk, the number of elements of a[0..n) below v, over c
// elsewhere; the prefix sums of the histogram stored at the values
function rank_table(c: array<int, int>, a: array<int, int>, n: Nat, kk: Nat): array<int, int>

lemma {:rw} rank_table_def(c0: array<int, int>, a: array<int, int>, n: Nat, kk: Nat, hs: List<int>)
  ensures current(stores(c0, ⌊counter(0, 1, kk)⌋,
      ⌊sums(0, maps(for ⌊counter(0, 1, kk)⌋, hs yield v, h :: count(v, selects(a, ⌊counter(0, 1, n)⌋))))⌋))
    == rank_table(c0, a, n, kk)

// the scatter: each element a[k] is stored at its start position plus the number of equal elements before it, which
// the increments of the table count; the result is sorted on 0, ..., n - 1 if the keys are in [0, kk), and the
// stored elements are those of a
lemma {:rw} sorted_scatter(b0: array<int, int>, c2: array<int, int>, a: array<int, int>, n: Nat, kk: Nat, s: int, hs: List<int>, hs2: List<int>, hs3: List<int>, kb: int, Iv: Trace<int>)
  requires s == integer(n)
  requires keys_below(a, s, kb) && kb == integer(kk)
  requires Iv == counter(0, 1, n)
  requires hs3 == ⌊Iv⌋
  ensures sorted(current(stores(b0,
      maps(for ⌊counter(0, 1, n)⌋, ⌊trace(rank_table(c2, a, n, kk), for ⌊counter(0, 1, n)⌋, hs do c, k, h :: c[a[k] := c[a[k]] + 1])⌋, hs2 yield k, c, h :: c[a[k]]),
      selects(a, hs3))), 0, s)
    <==> true

lemma {:rw} count_scatter(b0: array<int, int>, c2: array<int, int>, a: array<int, int>, n: Nat, kk: Nat, s: int, hs: List<int>, hs2: List<int>, hs3: List<int>, x: int, kb: int, Iv: Trace<int>)
  requires s == integer(n)
  requires keys_below(a, s, kb) && kb == integer(kk)
  requires Iv == counter(0, 1, n)
  requires hs3 == ⌊Iv⌋
  ensures count(x, selects(current(stores(b0,
      maps(for ⌊counter(0, 1, n)⌋, ⌊trace(rank_table(c2, a, n, kk), for ⌊counter(0, 1, n)⌋, hs do c, k, h :: c[a[k] := c[a[k]] + 1])⌋, hs2 yield k, c, h :: c[a[k]]),
      selects(a, hs3))), ⌊counter(0, 1, n)⌋))
    == count(x, selects(a, ⌊counter(0, 1, n)⌋))

method main(a: array<int, int>, n: int, k: int) returns (b: array<int, int>)
  requires 0 <= n && 0 < k
  requires keys_below(a, n, k)
  ensures sorted(b, 0, n)
  ensures forall x: int :: count(x, selects(b, ⌊counter(0, 1, natural(n))⌋)) == count(x, selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var c: array<int, int>;
  var i: int;
  var v: int;
  var s: int;
  var t: int;
  v := 0;
  while v < k
  {
    c := c[v := 0];
    v := v + 1;
  }
  i := 0;
  while i < n
  {
    c := c[a[i] := c[a[i]] + 1];
    i := i + 1;
  }
  s := 0;
  v := 0;
  while v < k
  {
    t := c[v];
    c := c[v := s];
    s := s + t;
    v := v + 1;
  }
  i := 0;
  while i < n
  {
    b := b[c[a[i]] := a[i]];
    c := c[a[i] := c[a[i]] + 1];
    i := i + 1;
  }
}
