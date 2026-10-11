// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/merge.dfy
// the merge of the sorted ranges a[0..m) and b[0..n) into c[0..m + n): a single loop over k == i + j with two
// data-dependent pointers i and j, and a conditional store; the permutation is stated by the counts of each value
// (a multiset), since the elements move between arrays
//
// status: verified with -teq -simplify, both sorted and the counts; the pointers i and j are traces over each other
// (I over ⌊J⌋, J over ⌊I⌋), the array a trace over both with the guard n <= j || i < m && a[i] <= b[j]; three
// workarounds of the matcher (NOTES.md): (1) a literal disjunctive guard is never matched, hence the guard G(i, j)
// and the stored values U(i, j), V(i, j) are higher-order, pinned by quantified side conditions, which the simplifier
// decides by beta reduction; (2) the lists is and js of the pointers are tied to their traces by open trace
// variables Iv == trace(...) matched against the hypotheses, then is == ⌊Iv⌋ (a closed equation with the trace is
// not decided); (3) the whole atom sorted(current(...), 0, s) is the left-hand side with s == m + n as a side
// condition, since a variable argument of sorted is not expanded by its definition for subterm rewriting and a
// pattern m + n of two variables is not matched; the counts likewise rewrite selects(current(...), ...) to the
// abstract list merged(a, m, b, n), whose counts are those of both ranges (count_merged); a reduced program with the
// same loop but the postcondition c[0] == 0 was matched even by literal patterns

function sorted(a: array<int, int>, lo: int, hi: int): bool

// the merge by the loop over k == i + j with the pointers i and j, traces over each other: the guard and the stored
// values are higher-order, pinned by quantified side conditions, since a literal disjunctive guard is not matched
lemma {:rw} sorted_merge_loop(a: array<int, int>, m: int, b: array<int, int>, n: int, c0: array<int, int>, nn: Nat,
                              is: List<int>, js: List<int>, s: int, G: (int, int) -> bool, U: (int, int) -> int, V: (int, int) -> int, Iv: Trace<int>, Jv: Trace<int>)
  requires s == m + n && m + n <= integer(nn)
  requires 0 <= m && 0 <= n && sorted(a, 0, m) && sorted(b, 0, n)
  requires forall i: int, j: int :: G(i, j) <==> (n <= j || i < m && a[i] <= b[j])
  requires forall i: int, j: int :: U(i, j) == a[i]
  requires forall i: int, j: int :: V(i, j) == b[j]
  requires Iv == trace(0, for ⌊counter(0, 1, nn)⌋, js do i, k, j :: case G(i, j) => i + 1 case !G(i, j) => i)
  requires is == ⌊Iv⌋
  requires Jv == trace(0, for ⌊counter(0, 1, nn)⌋, is do j, k, i :: case G(i, j) => j case !G(i, j) => j + 1)
  requires js == ⌊Jv⌋
  ensures sorted(current(trace(c0, for ⌊counter(0, 1, nn)⌋, is, js do c, k, i, j :: case G(i, j) => c[k := U(i, j)] case !G(i, j) => c[k := V(i, j)])), 0, s)
    <==> true

// the values of the merge on the positions 0, ..., m + n - 1
function merged(a: array<int, int>, m: int, b: array<int, int>, n: int): List<int>

lemma {:rw} selects_merge_loop(a: array<int, int>, m: int, b: array<int, int>, n: int, c0: array<int, int>, nn: Nat,
                               is: List<int>, js: List<int>, s: int, G: (int, int) -> bool, U: (int, int) -> int, V: (int, int) -> int,
                               Iv: Trace<int>, Jv: Trace<int>)
  requires s == m + n && m + n <= integer(nn)
  requires 0 <= m && 0 <= n
  requires forall i: int, j: int :: G(i, j) <==> (n <= j || i < m && a[i] <= b[j])
  requires forall i: int, j: int :: U(i, j) == a[i]
  requires forall i: int, j: int :: V(i, j) == b[j]
  requires Iv == trace(0, for ⌊counter(0, 1, nn)⌋, js do i, k, j :: case G(i, j) => i + 1 case !G(i, j) => i)
  requires is == ⌊Iv⌋
  requires Jv == trace(0, for ⌊counter(0, 1, nn)⌋, is do j, k, i :: case G(i, j) => j case !G(i, j) => j + 1)
  requires js == ⌊Jv⌋
  ensures selects(current(trace(c0, for ⌊counter(0, 1, nn)⌋, is, js do c, k, i, j :: case G(i, j) => c[k := U(i, j)] case !G(i, j) => c[k := V(i, j)])), ⌊counter(0, 1, natural(s))⌋)
    == merged(a, m, b, n)

// the merge has the values of both ranges
lemma {:rw} count_merged(a: array<int, int>, m: int, b: array<int, int>, n: int, x: int)
  requires 0 <= m && 0 <= n
  ensures count(x, merged(a, m, b, n)) == count(x, selects(a, ⌊counter(0, 1, natural(m))⌋)) + count(x, selects(b, ⌊counter(0, 1, natural(n))⌋))

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
