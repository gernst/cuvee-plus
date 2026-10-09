// ./Cuvee.sh -teq -simplify examples/dafny/sorting/selection_sort.dfy
// selection sort with nested loops: the inner loop finds the position m of the minimum of b[i..n), which is swapped
// to position i
//
// status (interim): open; the trace equation system has the outer array trace
// B == trace(a, for ⌊K⌋, ⌊I⌋, M? do b, k, i, m :: b[k := b[m]][m := b[k]]), a trace of swaps of k with the result m
// of the inner loop, and the inner loop as fragments of the iteration constraint of the outer loop, among them
// M == trace(k, for ⌊J⌋ do m, j :: case b[j] < b[m] => j case b[m] <= b[j] => m), the position of the minimum, and
// J == sums(k + 1, maps(for ⌊K'⌋ yield 1)), which is counter(k + 1, 1, n') in the context of its iteration (see
// invs_counter_equation.dfy and invs_fragments.dfy for the two problems of nested loops);
// perm(b, a) follows from perm_swaps of perm.dfy as soon as the positions m are a dependency as here: the lemma
// below is its instance with the positions k and m; sorted(b, 0, n) needs the summary of the inner loop,
// m == argmin(b, k, n) with lemmas k <= argmin(b, k, n) < n and b[argmin(b, k, n)] <= b[j] for k <= j < n, and a lemma
// on the trace of swaps with the minimum, like sorted_bubble_passes in bubble_sort.dfy

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// a trace of swaps at positions that depend on the state and the iteration preserves the permutation (perm.dfy)
lemma {:rw} perm_swaps(a: array<int, int>, b: array<int, int>, ks: List<int>, hs: List<int>,
                       P: (array<int, int>, int, int) -> int, Q: (array<int, int>, int, int) -> int)
  ensures perm(current(trace(a, for ks, hs do x, k, h :: x[P(x, k, h) := x[Q(x, k, h)]][Q(x, k, h) := x[P(x, k, h)]])), b)
    <==> perm(a, b)

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
