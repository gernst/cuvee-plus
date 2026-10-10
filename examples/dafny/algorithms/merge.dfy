// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/merge.dfy
// the merge of the sorted ranges a[0..m) and b[0..n) into c[0..m + n): a single loop over k == i + j with two
// data-dependent pointers i and j, and a conditional store; the permutation is stated by the counts of each value
// (a multiset), since the elements move between arrays
//
// status: open; no lemma matches the trace of c, not even a fully higher-order pattern
// current(trace(c0, for ⌊counter(0, 1, nn)⌋, is, js, ks do c, k, i, j, k2 :: case G(i, j) => c[k := U(i, j)] case !G(i, j) => c[k := V(i, j)]))
// nor the same trace as a fold; the pointers i and j are traces over each other (I over ⌊J⌋, J over ⌊I⌋), and the
// guard is a disjunction; which of the two blocks the matching is not isolated yet (see NOTES.md); the intended
// lemmas: the merge as an abstract function merge(a, m, b, n), sorted and the counts of its values by lemmas, and
// a summary of the loop whose side conditions equate is and js with the traces of the pointers

function sorted(a: array<int, int>, lo: int, hi: int): bool

method main(a: array<int, int>, m: int, b: array<int, int>, n: int) returns (c: array<int, int>)
  requires 0 <= m && 0 <= n
  requires sorted(a, 0, m) && sorted(b, 0, n)
  ensures sorted(c, 0, m + n)
  ensures forall x: int :: count(x, selects(c, ⌊counter(0, 1, natural(m + n))⌋))
    == count(x, selects(a, ⌊counter(0, 1, natural(m))⌋)) + count(x, selects(b, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  var k: int;
  i := 0;
  j := 0;
  k := 0;
  while k < m + n
  {
    if n <= j || (i < m && a[i] <= b[j]) {
      c := c[k := a[i]];
      i := i + 1;
    } else {
      c := c[k := b[j]];
      j := j + 1;
    }
    k := k + 1;
  }
}
