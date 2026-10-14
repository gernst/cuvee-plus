// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/selection_sort.dfy
// selection sort with nested loops: the inner loop finds the position m of the minimum of b[i..n), which is swapped
// to position i
//
// status (Oct 14, 2026): verified with -teq -prove, both sorted(b, 0, n) and perm(b, a); a wrong postcondition,
// sorted(b, 0, n + 1) or perm(b, a[0 := 1]), leaves a goal;
// the inner loop is a value of the outer update: the trace of b over the counter, the numbers of inner iterations N?
// (a choice) and the counter of i swaps i with the current value of the selection trace of the inner loop, which
// current_selection names argmin(b, i, i + 1 + integer(nn)); the inner test and exit are the two constraints of the
// outer loop on the choice, nn == zero || i + 1 < n && integer(nn) + i < n and n <= integer(nn) + i + 1, which fix
// i + 1 + integer(nn) == n for i < n; the induction sorted_selection_steps takes them as side conditions and states
// the invariant (a sorted prefix below the rest) as a quantified condition, decided by the two step lemmas, and
// perm(b, a) follows from perm_steps_choice and perm_swap_any;
// the constraints are matched with open lists, identified by equations afterwards: a closed instance would be
// simplified first, which drops the unused dependency ⌊K⌋ of the counter of the iterations that the facts keep, so
// that it is not found among them

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool
function partitioned(b: array<int, int>, lo: int, mid: int, hi: int): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the position of the minimum of b[lo..hi), lo if the range is empty
function argmin(b: array<int, int>, lo: int, hi: int): int

// the inner loop: the position of the minimum of b[i..i + 1 + nn), scanned from i + 1 for nn steps
lemma {:rw} current_selection(b: array<int, int>, i: int, nn: Nat)
  ensures current(trace(i, for ⌊counter(0, 1, nn)⌋, ⌊counter(i + 1, 1, nn)⌋ do m, k, j ::
            case b[j] < b[m] => j case b[m] <= b[j] => m))
    == argmin(b, i, i + 1 + integer(nn))

// one step of selection sort keeps the sorted prefix below the rest, given the constraints of the inner loop, which
// fix i + 1 + nn == n; n is bound by the condition on partitioned, the others are looked up among the hypotheses
lemma {:rw} sorted_swap_argmin_nat(b: array<int, int>, i: int, nn: Nat, n: int)
  requires partitioned(b, 0, i, n)
  requires i < n && n <= integer(nn) + i + 1 && (nn == zero || i + 1 < n && integer(nn) + i < n) && sorted(b, 0, i)
  ensures sorted(b[i := b[argmin(b, i, i + 1 + integer(nn))]][argmin(b, i, i + 1 + integer(nn)) := b[i]], 0, i + 1)
    <==> true

lemma {:rw} partitioned_swap_argmin_nat(b: array<int, int>, i: int, nn: Nat, n: int)
  requires partitioned(b, 0, i, n)
  requires i < n && n <= integer(nn) + i + 1 && (nn == zero || i + 1 < n && integer(nn) + i < n) && sorted(b, 0, i)
  ensures partitioned(b[i := b[argmin(b, i, i + 1 + integer(nn))]][argmin(b, i, i + 1 + integer(nn)) := b[i]],
                      0, i + 1, n)
    <==> true

// the induction over the counter, the choice of the numbers of inner iterations and the loop counter, with the two
// constraints of the inner loop on the choice as closed side conditions
lemma {:rw} sorted_selection_steps(a: array<int, int>, n: int, m: Nat, ns: List<Nat>, ks: List<int>, is: List<int>,
                                   ns2: List<Nat>, ks3: List<int>, is3: List<int>, ns3: List<Nat>,
                                   F: (array<int, int>, int, Nat) -> array<int, int>)
  requires n == integer(m)
  requires invs(for ks, is, ns2 check k, i, nn :: n <= integer(nn) + i + 1)
  requires is == ⌊counter(0, 1, m)⌋ && ns2 == ns
  requires invs(for ks3, is3, ns3 check k, i, nn :: nn == zero || i + 1 < n && integer(nn) + i < n)
  requires is3 == ⌊counter(0, 1, m)⌋ && ns3 == ns
  requires forall b: array<int, int>, i: int, nn: Nat ::
    0 <= i < n && n <= integer(nn) + i + 1 && (nn == zero || i + 1 < n && integer(nn) + i < n)
      && sorted(b, 0, i) && partitioned(b, 0, i, n)
      ==> sorted(F(b, i, nn), 0, i + 1) && partitioned(F(b, i, nn), 0, i + 1, n)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋, ns, ⌊counter(0, 1, m)⌋ do b, k, nn, i :: F(b, i, nn))), 0, n)
    <==> true

// a swap is a permutation
lemma {:rw} perm_swap_any(x: array<int, int>, p: int, q: int)
  ensures perm(x[p := x[q]][q := x[p]], x) <==> true

// a trace of steps that preserve the permutation, which also read the choice and the loop counter
lemma {:rw} perm_steps_choice(a: array<int, int>, c: array<int, int>, ks: List<int>, ns: List<Nat>, is: List<int>,
                              F: (array<int, int>, int, Nat) -> array<int, int>)
  requires forall b: array<int, int>, i: int, nn: Nat :: perm(F(b, i, nn), b)
  ensures perm(current(trace(a, for ks, ns, is do b, k, nn, i :: F(b, i, nn))), c) <==> perm(a, c)

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var j: int;
  var m: int;
  var t: int;
  b := a;
  i := 0;
  while i < n
  {
    m := i;
    j := i + 1;
    while j < n
    {
      if b[j] < b[m] {
        m := j;
      }
      j := j + 1;
    }
    t := b[i];
    b[i] := b[m];
    b[m] := t;
    i := i + 1;
  }
}
