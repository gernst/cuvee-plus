// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/counting_sort.dfy
// counting sort of a[0..n) with keys in [0, k): a histogram, its prefix sums as the starting positions, and the
// scatter of the elements; three loops in sequence, whose summaries feed each other
//
// status: open; a histogram lemma current_trace_histogram (the increments at the keys a[k] add count(v, selects(a, ...))
// at each value v) summarizes the second loop, after which the third loop is the prefix sums of the counts,
// S == sums(0, maps(for ⌊K⌋, ⌊V⌋ yield k, v :: count(k, selects(a, ⌊counter(0, 1, n)⌋)))); the fourth loop scatters each
// element to c[a[k]], the number of smaller elements plus the number of equal ones before it, and increments it; the
// correctness (the positions are a permutation of 0, ..., n - 1 that respects the order) is a chain of lemmas on
// stores at positions given by a trace, which is not attempted

function sorted(a: array<int, int>, lo: int, hi: int): bool

method main(a: array<int, int>, n: int, k: int) returns (b: array<int, int>)
  requires 0 <= n && 0 < k
  requires forall i: int :: 0 <= i < n ==> 0 <= a[i] < k
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
