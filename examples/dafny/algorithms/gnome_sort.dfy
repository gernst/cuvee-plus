// ./Cuvee.sh -teq -entry main -simplify examples/dafny/algorithms/gnome_sort.dfy
// gnome sort: a single loop whose position moves down at a descent and up otherwise, so that the number of
// iterations is not a counter; expected to stay open as a negative example of the loop shapes that trace equation
// systems model, but verified by a summary lemma on the whole atom of the postcondition
//
// status: verified with -teq -simplify (Oct 11, 2026, night; NOTES.md, finding 36): the position i and the array b
// are traces over each other with the guard b[i - 1] <= b[i], the number of iterations is not related to n (the exit
// n <= i only bounds it from below), and the swaps are at i and i - 1, arithmetic on a bound variable; the lemma
// sorted_gnome below states the invariant sorted(b, 0, i) directly for this shape, with the guard and the positions
// pinned; the wrong postcondition sorted(b, 0, n + 1) leaves a goal (pending/gnome_wrong.dfy)

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the invariant of gnome sort is sorted(b, 0, i): a step up (the guard G holds) extends the sorted prefix, a step
// down with a swap at P(i) == i - 1 and Q(i) == i keeps the prefix below sorted; at the exit n <= i the prefix covers
// the range; the lemma is on the whole atom of the postcondition (merge.dfy), with the guard and the positions
// higher-order and pinned, since the literal i - 1 is not matched; the trace of the position is tied by an open trace
// variable Iv2, matched against its equation, and identified with the dependency Iv of the left-hand side, likewise
// the trace of the array Bv as the dependency of the position's trace (sound ties, no condition mentions the
// left-hand side); the step 1 and -1 of the position are variables, since literals in patterns are not matched
lemma {:rw} sorted_gnome(a: array<int, int>, n: int, u: int, d: int, x: int, Kv: Trace<int>, Iv: Trace<int>, Iv2: Trace<int>,
                         Kv2: Trace<int>, Bv: Trace<array<int, int>>, Bv2: Trace<array<int, int>>,
                         G: (int, array<int, int>) -> bool, P: int -> int, Q: int -> int)
  requires Bv == trace(a, for ⌊Kv⌋, ⌊Iv2⌋ do b, k, i :: case G(i, b) => b case !G(i, b) => b[Q(i) := b[P(i)]][P(i) := b[Q(i)]])
  requires Iv2 == Iv
  requires Iv2 == trace(1, for ⌊Kv2⌋, ⌊Bv2⌋ do i, k, b :: case G(i, b) => i + u case !G(i, b) => i + d)
  requires Kv2 == Kv && Bv2 == Bv && u == 1 && d == -1
  requires forall i: int, b: array<int, int> :: G(i, b) <==> (i == 0 || b[i - 1] <= b[i])
  requires forall i: int :: P(i) == i - 1
  requires forall i: int :: Q(i) == i
  requires x == current(Iv)
  requires n <= x
  ensures sorted(current(trace(a, for ⌊Kv⌋, ⌊Iv⌋ do b, k, i :: case G(i, b) => b case !G(i, b) => b[Q(i) := b[P(i)]][P(i) := b[Q(i)]])), 0, n)
    <==> true

// every step is the identity or a swap, so the result is a permutation of the initial array, for any guard and
// positions
lemma {:rw} perm_gnome(a: array<int, int>, c: array<int, int>, ks: List<int>, is: List<int>,
                       G: (int, array<int, int>) -> bool, P: int -> int, Q: int -> int)
  ensures perm(current(trace(a, for ks, is do b, k, i :: case G(i, b) => b case !G(i, b) => b[Q(i) := b[P(i)]][P(i) := b[Q(i)]])), c)
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
