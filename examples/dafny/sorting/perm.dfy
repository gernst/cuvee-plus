// ./Cuvee.sh -teq -simplify examples/dafny/sorting/perm.dfy
// permutations by swaps in single loops: a reversal of a[0..n), and swaps with arbitrary positions
//
// status: verified with -teq -simplify;
// perm(a, b) is an abstract predicate, a is a permutation of b as a total map on the indices, which a swap preserves,
// and a trace of swaps too, whose positions P and Q may depend on the state and on the iteration (a higher-order
// pattern, bound like the cases of incs in bsearch.dfy); the goal perm(current(trace(...)), a) becomes perm(a, a)

function perm(a: array<int, int>, b: array<int, int>): bool

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// a swap preserves the permutation
lemma {:rw} perm_swap(a: array<int, int>, b: array<int, int>, p: int, q: int)
  ensures perm(a[p := a[q]][q := a[p]], b) <==> perm(a, b)

// a trace of swaps at positions that depend on the state and the iteration preserves the permutation
lemma {:rw} perm_swaps(a: array<int, int>, b: array<int, int>, ks: List<int>, hs: List<int>,
                       P: (array<int, int>, int, int) -> int, Q: (array<int, int>, int, int) -> int)
  ensures perm(current(trace(a, for ks, hs do x, k, h :: x[P(x, k, h) := x[Q(x, k, h)]][Q(x, k, h) := x[P(x, k, h)]])), b)
    <==> perm(a, b)

method reverse(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures perm(b, a)
{
  var i: int;
  var t: int;
  b := a;
  i := 0;
  while i < n - 1 - i
  {
    t := b[i];
    b[i] := b[n - 1 - i];
    b[n - 1 - i] := t;
    i := i + 1;
  }
}

method shuffle(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures perm(b, a)
{
  var i: int;
  var m: int;
  var t: int;
  b := a;
  i := 0;
  while i < n
  {
    m := *;
    t := b[i];
    b[i] := b[m];
    b[m] := t;
    i := i + 1;
  }
}
