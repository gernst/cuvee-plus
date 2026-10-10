// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/insertion_sort.dfy
// insertion sort with nested loops: the inner loop moves b[i] down by adjacent swaps while it is smaller than its
// predecessor
//
// status: perm(b, a) is proved, sorted(b, 0, n) remains open, since the inner loop cannot be summarized: its swaps
// are at j and j - 1, arithmetic on a bound variable of the trace, which patterns do not match (TODO.md); the
// variant insertion_sort2.dfy with two pointers j and p == j - 1 is verified;
// the trace equation system is like that of bubble_sort.dfy: the outer array trace is the chain of the results of
// the inner loop, B == results(a, ⌊K⌋, B?), and the inner loop is a trace of swaps
// B' == trace(b, for ⌊J⌋ do x, j :: x[j := x[j + -1]][j + -1 := x[j]]) over a counter J from i down by 1, with the
// iteration constraints 0 < j and x[j] < x[j + -1]; a fold of this trace into a function insert_pass(b, js) does not
// match, since its pattern has arithmetic on the bound variable j (TODO.md), hence perm_results_swaps abstracts the
// positions of the swaps by P and Q, like perm_swaps in perm.dfy, which closes perm(b, a);
// sorted(b, 0, n) needs the summary of the inner loop as an insertion, insert(b, i), from the fragments of the
// iteration constraint like current_results_bubble in bubble_sort.dfy, with the exit !(0 < j && b[j] < b[j - 1])
// on the final array and the iteration constraint 0 < j && x[j] < x[j - 1] of the swaps, lemmas that insert(b, i)
// keeps sorted(b, 0, i) and extends it to sorted(b, 0, i + 1), and a lemma on the outer trace like
// sorted_bubble_passes

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// the outer trace: the initial value followed by the results of the inner loop (bubble_sort.dfy)
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// each result is the current value of a trace of swaps that starts from the previous result, at positions P and Q
// that depend on the state and the inner iteration (perm_swaps of perm.dfy)
lemma {:rw} perm_results_swaps(a: array<int, int>, c: array<int, int>, ks: List<int>, bs: List<array<int, int>>,
                               Bs: List<Trace<array<int, int>>>, Js: List<Trace<int>>,
                               P: (array<int, int>, int) -> int, Q: (array<int, int>, int) -> int)
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Bs, Js check k, x, B, J ::
    B == trace(x, for ⌊J⌋ do y, j :: y[P(y, j) := y[Q(y, j)]][Q(y, j) := y[P(y, j)]]))
  ensures perm(current(results(a, ks, bs)), c) <==> perm(a, c)

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
