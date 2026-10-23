// ./Cuvee.sh -teq -include teq:sorted -include teq:aggregation -entry main -prove examples/dafny/algorithms/insertion_sort2.dfy
// insertion sort with nested loops, with two pointers j and p == j - 1 in the inner loop, such that the positions
// of the swaps are counters: insertion_sort.dfy swaps b[j] and b[j - 1], arithmetic on a bound variable of the
// trace (the principle of reverse.dfy: two pointers instead of index arithmetic)
//
// status (Oct 16, 2026): verified with -teq -prove, both sorted(b, 0, n) and perm(b, a); a wrong postcondition,
// sorted(b, 0, n + 1) or perm(b, a[0 := 1]), leaves a goal; as in bubble_sort.dfy, the inner loop is a value of the
// outer update, folded into insert_pass(b, i, k, nn) over the numbers of inner iterations N? (a choice); the outer
// loop records two constraints of each pass, that every swap had b[j] < b[p] and the exit (j == 0 or b[j] >= b[p]),
// over the history of the outer trace; the induction sorted_insert_steps takes both as side conditions, with
// higher-order predicates matched against them, and decides its quantified step condition by sorted_insert_pass;
// the step is stated over k alone (the prefix [0, k + 1) before, [0, k + 2) after), since the engine substitutes
// i == k + 1 in the bound of sorted but not in the arguments of the pass; perm(b, a) follows from perm_steps_three
// and perm_insert_pass

// one pass of the inner loop: the swaps of the positions j and q, counters down from i and p
function {:fold} insert_pass(b: array<int, int>, i: int, p: int, nn: Nat): Trace<array<int, int>>
{
  trace(b, for ⌊counter(0, 1, nn)⌋, ⌊counter(i, -1, nn)⌋, ⌊counter(p, -1, nn)⌋ do x, kk, j, q :: x[j := x[q]][q := x[j]])
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
  requires invs(for ⌊counter(0, 1, nn)⌋, ⌊insert_pass(b, i, p, nn)⌋, ⌊counter(i, -1, nn)⌋, ⌊counter(p, -1, nn)⌋
                check kk, y, j, q :: y[j] < y[q])
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
  var p: int;
  var t: int;
  b := a;
  i := 1;
  while i < n
  {
    j := i;
    p := i - 1;
    while 0 < j && b[j] < b[p]
    {
      t := b[j];
      b[j] := b[p];
      b[p] := t;
      j := j - 1;
      p := p - 1;
    }
    i := i + 1;
  }
}
