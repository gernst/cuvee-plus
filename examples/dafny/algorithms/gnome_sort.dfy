// ./Cuvee.sh -teq -entry main -prove examples/dafny/algorithms/gnome_sort.dfy
// gnome sort: a single loop whose position moves down at a descent and up otherwise, so that the number of
// iterations is not a counter
//
// status (Oct 14, 2026): verified with -teq -prove, both sorted(b, 0, n) and perm(b, a); a wrong postcondition,
// sorted(b, 0, n + 1) or perm(b, a[0 := 1]), leaves a goal;
// the position i and the array b read each other through the guard i == 0 || b[i - 1] <= b[i], so they form one
// trace S of two accumulators; the lemma sorted_gnome states the invariant sorted(b, 0, i) of that trace as a whole,
// which holds for every run of its update (the guards are complementary), as a rule on the atom of the
// postcondition: the trace is a rule variable Sv, matched against the variable of the goal, whose equation is an open
// condition, and the position is read from the facts by an open x == current(Sv).0, so that no condition contains the
// trace itself (whose views would be recomputed for each instance) or a read of its component (which is replaced by
// its view before it is looked up); with the exit n <= i, the prefix covers the range

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the invariant of gnome sort: b[0..i) is sorted after every step (a step up past an element in order with its
// predecessor extends the sorted prefix, a swap down keeps the prefix below the new position sorted), and the
// position stays nonnegative; hence every prefix up to the position is sorted
lemma {:rw} sorted_gnome(a: array<int, int>, ks: List<int>, n: int, x: int, Sv: Trace<(int, array<int, int>)>)
  requires Sv == trace(1, a, for ks do i, b, k ::
                   case i == 0 || b[i - 1] <= b[i] => i + 1
                   case !(i == 0 || b[i - 1] <= b[i]) => i - 1,
                   case i == 0 || b[i - 1] <= b[i] => b
                   case !(i == 0 || b[i - 1] <= b[i]) => b[i := b[i - 1]][i - 1 := b[i]])
  requires x == current(Sv).0
  requires 0 <= n && n <= x
  ensures sorted(current(Sv).1, 0, n) <==> true

// every step is the identity or a swap, so the result is a permutation of the initial array, for any guard and
// positions; it matches the view of the array component, whose dependency is the history of the position
lemma {:rw} perm_gnome(a: array<int, int>, c: array<int, int>, ks: List<int>, is: List<int>,
                       G: (int, array<int, int>) -> bool, P: int -> int, Q: int -> int)
  ensures perm(current(trace(a, for ks, is do b, k, i ::
                 case G(i, b) => b case !G(i, b) => b[Q(i) := b[P(i)]][P(i) := b[Q(i)]])), c)
    <==> perm(a, c)

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var t: int;
  b := a;
  i := 1;
  while i < n
  {
    if i == 0 || b[i - 1] <= b[i] {
      i := i + 1;
    } else {
      t := b[i];
      b[i] := b[i - 1];
      b[i - 1] := t;
      i := i - 1;
    }
  }
}
