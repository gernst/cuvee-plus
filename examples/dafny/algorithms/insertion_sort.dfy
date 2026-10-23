// ./Cuvee.sh -teq -include teq:sorted -include teq:aggregation -entry main -prove examples/dafny/algorithms/insertion_sort.dfy
// insertion sort with nested loops: the inner loop moves b[i] down by adjacent swaps while it is smaller than its
// predecessor
//
// status (Oct 16, 2026): verified with -teq -prove, both sorted(b, 0, n) and perm(b, a); a wrong postcondition,
// sorted(b, 0, n + 1) or perm(b, a[0 := 1]), leaves a goal; the lemmas of insertion_sort2.dfy, except for the pass:
// -teq states the position j - 1 of the swaps as k - kk over the outer and the inner counter (j == i - kk and
// i == k + 1), which the fold insert_pass matches with k as a parameter, such that no second pointer is needed

// one pass of the inner loop in iteration p of the outer loop: the swaps of the positions j, a counter down from i,
// and j - 1, which -teq states as p - kk over the inner counter kk (with i == p + 1)
function {:fold} insert_pass(b: array<int, int>, i: int, p: int, nn: Nat): Trace<array<int, int>>
{
  trace(b, for ⌊counter(0, 1, nn)⌋, ⌊counter(i, -1, nn)⌋ do x, kk, j :: x[j := x[-kk + p]][-kk + p := x[j]])
}

lemma {:rw} perm_insert_pass(b: array<int, int>, c: array<int, int>, i: int, p: int, nn: Nat)
  ensures perm(current(insert_pass(b, i, p, nn)), c) <==> perm(b, c)

lemma {:rw} perm_steps_three(a: array<int, int>, c: array<int, int>, ks: List<int>, ns: List<Nat>, is: List<int>,
                             F: (array<int, int>, int, Nat, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int, nn: Nat, i: int :: perm(F(b, k, nn, i), b)
  ensures perm(current(trace(a, for ks, ns, is do b, k, nn, i :: F(b, k, nn, i))), c) <==> perm(a, c)

// a pass on a sorted prefix b[0..i) with p == i - 1, every swap of which had y[j] < y[q], and which stopped at j == 0
// or at y[j] >= y[j - 1], sorts b[0..i + 1)
lemma {:rw} sorted_insert_pass(b: array<int, int>, i: int, p: int, nn: Nat)
  requires p + 1 == i && 0 <= p && integer(nn) <= p + 1 && sorted(b, 0, p + 1)
  requires invs(for ⌊counter(0, 1, nn)⌋, ⌊insert_pass(b, i, p, nn)⌋, ⌊counter(i, -1, nn)⌋
                check kk, y, j :: y[j] < y[-kk + p])
  requires !(integer(nn) <= p
             && current(insert_pass(b, i, p, nn))[-integer(nn) + p + 1] < current(insert_pass(b, i, p, nn))[-integer(nn) + p])
  ensures sorted(current(insert_pass(b, i, p, nn)), 0, p + 2) <==> true

// the induction for a growing sorted prefix from one element: the steps F in iteration k at i == k + 1 extend the
// sorted prefix b[0..i) by i, under the two constraints C and D that hold at every step (over the history of the
// trace), hence m steps sort b[0..len) if len <= m + 1
lemma {:rw} sorted_insert_steps(a: array<int, int>, len: int, m: Nat, ns: List<Nat>,
                                F: (array<int, int>, int, Nat, int) -> array<int, int>,
                                C: (int, int, array<int, int>, Nat) -> bool, D: (int, array<int, int>, int, Nat) -> bool)
  requires len <= integer(m) + 1
  requires invs(for ⌊counter(0, 1, m)⌋, ⌊counter(1, 1, m)⌋,
                    ⌊trace(a, for ⌊counter(0, 1, m)⌋, ns, ⌊counter(1, 1, m)⌋ do b, k, nn, i :: F(b, k, nn, i))⌋, ns
                check k, i, b, nn :: C(k, i, b, nn))
  requires invs(for ⌊counter(0, 1, m)⌋,
                    ⌊trace(a, for ⌊counter(0, 1, m)⌋, ns, ⌊counter(1, 1, m)⌋ do b, k, nn, i :: F(b, k, nn, i))⌋,
                    ⌊counter(1, 1, m)⌋, ns
                check k, b, i, nn :: D(k, b, i, nn))
  requires forall b: array<int, int>, k: int, nn: Nat, i: int ::
    0 <= k < integer(m) && i == k + 1 && integer(nn) <= k + 1 && sorted(b, 0, k + 1) && C(k, i, b, nn) && D(k, b, i, nn)
      ==> sorted(F(b, k, nn, i), 0, k + 2)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋, ns, ⌊counter(1, 1, m)⌋ do b, k, nn, i :: F(b, k, nn, i))), 0, len)
    <==> true

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var j: int;
  var t: int;
  b := a;
  i := 1;
  while i < n
  {
    j := i;
    while 0 < j && b[j] < b[j - 1]
    {
      t := b[j];
      b[j] := b[j - 1];
      b[j - 1] := t;
      j := j - 1;
    }
    i := i + 1;
  }
}
